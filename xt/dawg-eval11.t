#!/usr/bin/perl

use strict;
use warnings;
no warnings 'redefine';

BEGIN {
	no warnings 'once';
	$Error::TypeTiny::StackTrace	= 1;
}

package Translator 0.001 {
	use v5.14;
	use warnings;
	use Moo;
	use Data::Dumper;
	use namespace::clean;
	
	use Attean::RDF;
	use Scalar::Util qw(blessed);
	use Types::Standard qw(Bool ConsumerOf HashRef);
	has 'in_expr' => (is => 'rw', isa => Bool, default => 0);
	has 'base' => (is => 'rw', isa => ConsumerOf['Attean::IRI'], predicate => 'has_base');
	
	sub translate_query {
		my $class	= shift;
		my $query	= shift;
		my $parsed	= $query->{parsed};
		my $t		= $class->new();
		if (exists $parsed->{base} and my $base = $t->translate($parsed->{base})) {
			$t->base($base);
		}
		my $method	= $parsed->{method};
		my $algebra	= $t->translate($query->pattern);
		if (my $b = $parsed->{bindings}) {
			my @vars	= map { $t->translate($_) } @{ $b->{vars} };
			my $terms	= $b->{terms};
			my @bindings;
			foreach my $row (@$terms) {
				my %binding;
				foreach my $i (0 .. $#vars) {
					if (my $term = $row->[$i]) {
						$binding{ $vars[$i]->value }	= $t->translate($term);
					}
				}
				push(@bindings, Attean::Result->new( bindings => \%binding ));
			}
			my $table	= Attean::Algebra::Table->new( rows => \@bindings, variables => \@vars );
			$algebra	= Attean::Algebra::Join->new( children => [$table, $algebra] );
		}
		if ($method eq 'ASK') {
			$algebra	= Attean::Algebra::Ask->new( children => [$algebra] );
		}
		return $algebra;
	}
	
	sub translate {
		my $self	= shift;
		my $a		= shift;
		Carp::confess "Not a reference? " . Dumper($a) unless blessed($a);
		if ($a->isa('RDF::Query::Algebra::Construct')) {
			my $p		= $self->translate($a->pattern);
			my @triples	= @{ $a->triples || [] };
			if (scalar(@triples) == 1 and $triples[0]->isa('RDF::Query::Algebra::BasicGraphPattern')) {
				@triples	= $triples[0]->triples;
			}
			return Attean::Algebra::Construct->new( children => [$p], triples => [map { $self->translate($_) } @triples] );
		} elsif ($a->isa('RDF::Query::Algebra::Project')) {
			my $p	= $a->pattern;
			my $v	= $a->vars;
			my @vars	= map { variable($_->name) } @$v;
			return Attean::Algebra::Project->new(
				children	=> [ $self->translate($p) ],
				variables	=> [ @vars ],
			);
		} elsif ($a->isa('RDF::Query::Algebra::GroupGraphPattern')) {
			my @p	= map { $self->translate($_) } $a->patterns;
			if (scalar(@p) == 0) {
				return Attean::Algebra::BGP->new();
			} else {
				while (scalar(@p) > 1) {
					my ($l, $r)	= splice(@p, 0, 2);
					unshift(@p, Attean::Algebra::Join->new( children => [$l, $r] ));
				}
				return shift(@p);
			}
		} elsif ($a->isa('RDF::Query::Algebra::BasicGraphPattern')) {
			my @p	= map { $self->translate($_) } $a->triples;
			return Attean::Algebra::BGP->new( triples => \@p );
		} elsif ($a->isa('RDF::Query::Algebra::Triple')) {
			my @nodes	= map { $self->translate($_) } $a->nodes;
			return Attean::TriplePattern->new(@nodes);
		} elsif ($a->isa('RDF::Query::Node::Variable')) {
			my $value	= variable($a->isa("RDF::Query::Node::Variable::ExpressionProxy") ? ("." . $a->name) : $a->name);
			$value		= Attean::ValueExpression->new(value => $value) if ($self->in_expr);
			return $value;
		} elsif ($a->isa('RDF::Query::Node::Resource')) {
			my $value	= iri($a->uri_value);
			$value		= Attean::ValueExpression->new(value => $value) if ($self->in_expr);
			return $value;
		} elsif ($a->isa('RDF::Query::Node::Blank')) {
			my $value	= blank($a->blank_identifier);
			$value		= Attean::ValueExpression->new(value => $value) if ($self->in_expr);
			return $value;
		} elsif ($a->isa('RDF::Query::Node::Literal')) {
			my $value;
			if ($a->has_language) {
				$value	= langliteral($a->literal_value, $a->literal_value_language);
			} elsif ($a->has_datatype) {
				$value	= dtliteral($a->literal_value, $a->literal_datatype);
			} else {
				$value	= literal($a->literal_value);
			}
			$value	= Attean::ValueExpression->new(value => $value) if ($self->in_expr);
			return $value;
		} elsif ($a->isa('RDF::Query::Algebra::Limit')) {
			my $child	= $a->pattern;
			if ($child->isa('RDF::Query::Algebra::Offset')) {
				my $p	= $self->translate($child->pattern);
				return Attean::Algebra::Slice->new( children => [$p], limit => $a->limit, offset => $child->offset );
			} else {
				my $p	= $self->translate($child);
				return Attean::Algebra::Slice->new( children => [$p], limit => $a->limit );
			}
		} elsif ($a->isa('RDF::Query::Algebra::Offset')) {
			my $p	= $self->translate($a->pattern);
			return Attean::Algebra::Slice->new( children => [$p], offset => $a->offset );
		} elsif ($a->isa('RDF::Query::Algebra::Path')) {
			my $s		= $self->translate($a->start);
			my $o		= $self->translate($a->end);
			my $path	= $self->translate_path($a->path);
			return Attean::Algebra::Path->new( subject => $s, path => $path, object => $o );
		} elsif ($a->isa('RDF::Query::Algebra::NamedGraph')) {
			my $graph	= $self->translate($a->graph);
			my $p		= $self->translate($a->pattern);
			return Attean::Algebra::Graph->new( children => [$p], graph => $graph );
		} elsif ($a->isa('RDF::Query::Algebra::Filter')) {
			my $p		= $self->translate($a->pattern);
			my $expr	= $self->translate_expr($a->expr);
			return Attean::Algebra::Filter->new( children => [$p], expression => $expr );
		} elsif ($a->isa('RDF::Query::Expression::Binary')) {
			my $op	= $a->op;
			$op		= '=' if ($op eq '==');
			my @ops	= $a->operands;
			my @operands	= map { $self->translate($_) } @ops;
			my $expr	= Attean::BinaryExpression->new( operator => $op, children => \@operands );
			return $expr;
		} elsif ($a->isa('RDF::Query::Expression::Unary')) {
			my $op	= $a->op;
			$op		= '=' if ($op eq '==');
			my ($child)	= $a->operands;
			my $expr	= Attean::UnaryExpression->new( operator => $op, children => [$self->translate($child)] );
			return $expr;
		} elsif ($a->isa('RDF::Query::Algebra::Extend')) {
			my $p		= $self->translate($a->pattern);
			my $vars	= $a->vars;
			foreach my $v (@$vars) {
				if ($v->isa('RDF::Query::Expression::Alias')) {
					my $var		= variable($v->name);
					my $expr	= $v->expression;
					$p	= Attean::Algebra::Extend->new( children => [$p], variable => $var, expression => $self->translate_expr( $expr ) );
				} else {
					die "Unexpected extend expression: " . Dumper($v);
				}
			}
			return $p;
		} elsif ($a->isa('RDF::Query::VariableBindings')) {
			my %bindings;
			foreach my $v ($a->variables) {
				if (my $term = $a->{ $v }) {
					$bindings{ $v }	= $self->translate( $term );
				}
			}
			return Attean::Result->new( bindings => \%bindings );
		} elsif ($a->isa('RDF::Query::Algebra::Table')) {
			my @vars	= map { variable($_) } $a->variables;
			my @rows	= map { $self->translate($_) } $a->rows;
			return Attean::Algebra::Table->new( variables => \@vars, rows => \@rows );
		} elsif ($a->isa('RDF::Query::Algebra::Aggregate')) {
			my $p		= $self->translate($a->pattern);
			my @group;
			foreach my $g ($a->groupby) {
				if ($g->isa('RDF::Query::Expression::Alias')) {
					my $var		= $self->translate($g->alias);
					my $varexpr	= $self->translate_expr($g->alias);
					push(@group, $varexpr);
					my $expr	= $self->translate_expr( $g->expression );
					$p	= Attean::Algebra::Extend->new( children => [$p], variable => $var, expression => $expr );
				} else {
					push(@group, $self->translate_expr($g));
				}
			}
			my @ops		= $a->ops;
			
			my @aggs;
			foreach my $o (@ops) {
				my ($str, $op, $scalar_vars, @vars)	= @$o;
				my $operands	= [map { $self->translate_expr($_) } grep { blessed($_) } @vars];
				my $expr	= Attean::AggregateExpression->new(
					operator => $op,
					children => $operands,
					scalar_vars => $scalar_vars,
					variable => variable(".$str"),
				);
				push(@aggs, $expr);
			}
			return Attean::Algebra::Group->new(
				children	=> [$p],
				groupby		=> \@group,
				aggregates	=> \@aggs,
			);
		} elsif ($a->isa('RDF::Query::Algebra::Sort')) {
			my $p		= $self->translate($a->pattern);
			my @order	= $a->orderby;
			my @cmps;
			foreach my $o (@order) {
				my ($dir, $e)	= @$o;
				my $asc				= ($dir eq 'ASC');
				my $expr			= $self->translate_expr($e);
				push(@cmps, Attean::Algebra::Comparator->new(ascending => $asc, expression => $expr));
			}
			return Attean::Algebra::OrderBy->new( children => [$p], comparators => \@cmps );
		} elsif ($a->isa('RDF::Query::Algebra::Distinct')) {
			my $p		= $self->translate($a->pattern);
			return Attean::Algebra::Distinct->new( children => [$p] );
		} elsif ($a->isa('RDF::Query::Algebra::Minus')) {
			my $p		= $self->translate($a->pattern);
			my $m		= $self->translate($a->minus);
			return Attean::Algebra::Minus->new( children => [$p, $m] );
		} elsif ($a->isa('RDF::Query::Algebra::Union')) {
			my @p		= map { $self->translate($_) } $a->patterns;
			return Attean::Algebra::Union->new( children => \@p );
		} elsif ($a->isa('RDF::Query::Algebra::Optional')) {
			my $p		= $self->translate($a->pattern);
			my $o		= $self->translate($a->optional);
			return Attean::Algebra::LeftJoin->new( children => [$p, $o] );
		} elsif ($a->isa('RDF::Query::Algebra::SubSelect')) {
			my $q	= $a->query;
			my $p	= $self->translate_query($q);
			return $p;
		} elsif ($a->isa('RDF::Query::Expression::Function')) {
			my $uri		= $a->uri->uri_value;
			my @args	= map { $self->translate_expr($_) } $a->arguments;
			if ($uri eq 'sparql:logical-and') {
				my $algebra	= Attean::BinaryExpression->new( operator => '&&', children => [splice(@args, 0, 2)] );
				while (scalar(@args)) {
					$algebra	= Attean::BinaryExpression->new( operator => '&&', children => [$algebra, shift(@args)] );
				}
				return $algebra;
			} elsif ($uri eq 'sparql:logical-or') {
				my $algebra	= Attean::BinaryExpression->new( operator => '||', children => [splice(@args, 0, 2)] );
				while (scalar(@args)) {
					$algebra	= Attean::BinaryExpression->new( operator => '||', children => [$algebra, shift(@args)] );
				}
				return $algebra;
			} elsif ($uri =~ /^sparql:(.+)$/) {
				if ($1 eq 'exists') {
					# re-translate the pattern as a pattern, not an expression:
					my ($p)	= map { $self->translate_pattern($_) } $a->arguments;
					return Attean::ExistsExpression->new( pattern => $p );
				} else {
					return Attean::FunctionExpression->new( children => \@args, operator => $1, ($self->has_base ? (base => $self->base) : ()) );
				}
			} elsif ($uri =~ m<^http://www[.]w3[.]org/2001/XMLSchema#(?<cast>integer|decimal|float|double|string|boolean|dateTime)$>) {
				my $cast	= $+{cast};
				if ($cast =~ /^(?:integer|decimal|float|double)$/) {
					return Attean::CastExpression->new( children => \@args, datatype => iri($uri) );
				} elsif ($cast eq 'string') {
					return Attean::FunctionExpression->new( children => \@args, operator => 'STR', ($self->has_base ? (base => $self->base) : ()) );
				} elsif ($cast eq 'boolean') {
				
				} elsif ($cast eq 'dateTime') {
				
				}
			}
			warn "Unrecognized function: " . Dumper($uri, \@args);
		}
		Carp::confess "Unrecognized algebra " . ref($a);
	}

	sub translate_expr {
		my $self	= shift;
		my $a		= shift;
		my $prev	= $self->in_expr;
		$self->in_expr(1);
		my $expr	= $self->translate($a);
		$self->in_expr($prev);
		return $expr;
	}
	
	sub translate_pattern {
		my $self	= shift;
		my $a		= shift;
		my $prev	= $self->in_expr;
		$self->in_expr(0);
		my $expr	= $self->translate($a);
		$self->in_expr($prev);
		return $expr;
	}
	
	sub translate_path {
		my $self	= shift;
		my $path	= shift;
		if (blessed($path) and $path->isa('RDF::Query::Node::Resource')) {
			return Attean::Algebra::PredicatePath->new( predicate => $self->translate($path) );
		}
		
		my ($op, @args)	= @$path;
		if ($op eq '!') {
			my @nodes	= map { $self->translate($_) } @args;
			return Attean::Algebra::NegatedPropertySet->new( predicates => \@nodes );
		} elsif ($op eq '/') {
			my @paths	= map { $self->translate_path($_) } @args;
			foreach (@paths) {
				if ($_->does('Attean::API::IRI')) {
					$_	= Attean::Algebra::PredicatePath->new( predicate => $_ );
				}
			}
			return Attean::Algebra::SequencePath->new( children => \@paths );
		} elsif ($op eq '?') {
			my $path	= $self->translate_path(shift(@args));
			return Attean::Algebra::ZeroOrOnePath->new( children => [$path] );
		} elsif ($op eq '*') {
			my $path	= $self->translate_path(shift(@args));
			return Attean::Algebra::ZeroOrMorePath->new( children => [$path] );
		} elsif ($op eq '+') {
			my $path	= $self->translate_path(shift(@args));
			return Attean::Algebra::OneOrMorePath->new( children => [$path] );
		} elsif ($op eq '^') {
			my $path	= $self->translate_path(shift(@args));
			if ($path->does('Attean::API::IRI')) {
				$path	= Attean::Algebra::PredicatePath->new( predicate => $path );
			}
			return Attean::Algebra::InversePath->new( children => [$path] );
		} elsif ($op eq '|') {
			my @paths	= map { $self->translate_path($_) } @args;
			foreach (@paths) {
				if ($_->does('Attean::API::IRI')) {
					$_	= Attean::Algebra::PredicatePath->new( predicate => $_ );
				}
			}
			return Attean::Algebra::AlternativePath->new( children => \@paths );
		}
		die "Unrecognized path: $op";
	}
}

use v5.14;
use warnings;
no warnings 'once';
use autodie;
use Algorithm::Combinatorics qw(permutations);
use Benchmark qw(timethese);
use Data::Dumper;
use Encode qw(encode);
use File::Slurp;
use File::Temp qw(tempfile);
use Getopt::Long;
use LWP::MediaTypes qw(add_type);
use Regexp::Common qw /URI/;
use Scalar::Util qw(blessed reftype);
use Storable qw(dclone);
use Test::More;
use Text::CSV;
use Try::Tiny;
use URI::file;

add_type( 'application/rdf+xml' => qw(rdf xrdf rdfx) );
add_type( 'text/turtle' => qw(ttl) );
add_type( 'text/plain' => qw(nt) );
add_type( 'text/x-nquads' => qw(nq) );
add_type( 'text/json' => qw(json) );
add_type( 'text/html' => qw(html xhtml htm) );

use Attean;
use Attean::RDF;
use Attean::SimpleQueryEvaluator;

use RDF::Query;
use RDF::Trine qw(statement);
use RDF::Trine::Graph;
use RDF::Trine::Namespace qw(rdf rdfs xsd);
use RDF::Trine::Iterator qw(smap);

use Carp;
use HTTP::Request;
use HTTP::Response;
use HTTP::Message::PSGI;

our $RUN_UPDATE_TESTS	= 0;
our $RUN_QUERY_TESTS	= 1;
our $debug				= 0;
our $STRICT_APPROVAL	= 0;

require XML::Simple;

plan qw(no_plan);

my $PATTERN	= '';
my %args;

our $RUN_TESTS	= 1;
our $LIST_TESTS	= 0;

while (defined(my $opt = shift)) {
	if ($opt eq '-v') {
		$debug++;
	} elsif ($opt =~ /^-(.*)$/) {
		if ($1 eq 'list') {
			$RUN_TESTS	= 0;
			$LIST_TESTS	= 1;
		} elsif ($1 =~ 'stress=(\d+)') {
			$args{ 'stress' }	= $1;
		} else {
			$args{ $1 }	= 1;
		}
	} else {
		$PATTERN	= $opt;
	}
}

$ENV{RDFQUERY_THROW_ON_SERVICE}	= 1;

no warnings 'once';

if ($PATTERN) {
# 	$debug			= 1;
}

warn "PATTERN: ${PATTERN}\n" if ($PATTERN and $debug);

sub memory_model {
	my $store	= Attean->get_store('Memory')->new();
	my $model	= Attean::MutableQuadModel->new( store => $store );
	return $model;
}

my $model	= memory_model();
my @files;
if ($RUN_QUERY_TESTS) {
	push(@files, qw(
		aggregates
		bind
		bindings
		construct
		csv-tsv-res
		exists
		functions
		grouping
		json-res
		negation
		project-expression
		property-path
		subquery
	));
#		service
}
if ($RUN_UPDATE_TESTS) {
	push(@files, qw(
		add
		basic-update
		clear
		copy
		delete
		delete-data
		delete-insert
		delete-where
		drop
		move
		update-silent
	));
}
my @manifests	= map { glob( "xt/dawg11/$_/manifest.ttl" ) } @files;

my $class	= Attean->get_parser("turtle") || die "Failed to load parser for 'turtle'";
my $default_graph	= iri('http://graph/');
foreach my $file (@manifests) {
	my $path	= File::Spec->rel2abs($file);
	my $base	= iri("file://$path");
	my $parser	= $class->new( base => $base ) || die "Failed to construct parser for 'turtle'";
# 	warn "Parsing manifest $file\n" if $debug;
	open(my $fh, '<:utf8', $file);
	my $iter	= $parser->parse_iter_from_io($fh);
	my $quads	= $iter->as_quads($default_graph);
	$model->add_iter($quads);
}
warn "done parsing manifests" if $debug;

my $rs		= RDF::Trine::Namespace->new('http://www.w3.org/2001/sw/DataAccess/tests/result-set#');
my $mf		= RDF::Trine::Namespace->new('http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#');
my $ut		= RDF::Trine::Namespace->new('http://www.w3.org/2009/sparql/tests/test-update#');
my $rq		= RDF::Trine::Namespace->new('http://www.w3.org/2001/sw/DataAccess/tests/test-query#');
my $dawgt	= RDF::Trine::Namespace->new('http://www.w3.org/2001/sw/DataAccess/tests/test-dawg#');

{
	my @manifests	= $model->subjects( iri($rdf->type->uri_value), iri($mf->Manifest->uri_value) )->elements;
	foreach my $m (@manifests) {
# 		warn "Manifest: " . $m->as_string . "\n" if ($debug);
		my ($list)	= $model->objects( $m, iri($mf->entries->uri_value) )->elements;
		unless (blessed($list)) {
			warn "No mf:entries found for manifest " . $m->as_string . "\n";
		}
		my @tests	= $model->get_list( $default_graph, $list )->elements;
		foreach my $test (@tests) {
			unless ($test->value =~ /$PATTERN/) {
				next;
			}
			if ($LIST_TESTS) {
				say $test->value;
			}
			if ($RUN_TESTS) {
				if ($RUN_QUERY_TESTS) {
					my $et	= $model->count_quads($test, iri($rdf->type->uri_value), iri($mf->QueryEvaluationTest->uri_value));
					my $ct	= $model->count_quads($test, iri($rdf->type->uri_value), iri($mf->CSVResultFormatTest->uri_value));
					if ($et + $ct) {
						my ($name)	= $model->objects( $test, iri($mf->name->uri_value) )->elements;
						warn "### query eval test: " . $test->as_string . " >>> " . $name->value . "\n" if ($debug);
						my $count	= $args{ stress } || 1;
						query_eval_test( $model, $test, $count );
					}
				}
			
				if ($RUN_UPDATE_TESTS) {
					if ($model->count_quads($test, iri($rdf->type->uri_value), iri($ut->UpdateEvaluationTest->uri_value)) or $model->count_statements($test, iri($rdf->type->uri_value), iri($mf->UpdateEvaluationTest->uri_value))) {
						my ($name)	= $model->objects( $test, iri($mf->name->uri_value) );
						unless ($test->value =~ /$PATTERN/) {
							next;
						}
# 						warn "### update eval test: " . $test->as_string . " >>> " . $name->value . "\n" if ($debug);
# 						update_eval_test( $model, $test );
					}
				}
			}
		}
	}
}

sub query_eval_test {
	my $model		= shift;
	my $test		= shift;
	my $count		= shift || 1;
	
	my ($action)	= $model->objects( $test, iri($mf->action->uri_value) )->elements;
	my ($result)	= $model->objects( $test, iri($mf->result->uri_value) )->elements;
	my ($req)		= $model->objects( $test, iri($mf->requires->uri_value) )->elements;
	my ($approved)	= $model->objects( $test, iri($dawgt->approval->uri_value) )->elements;
	my ($queryd)	= $model->objects( $action, iri($rq->query->uri_value) )->elements;
	my ($data)		= $model->objects( $action, iri($rq->data->uri_value) )->elements;
	my @gdata		= $model->objects( $action, iri($rq->graphData->uri_value) )->elements;
	my @sdata		= $model->objects( $action, iri($rq->serviceData->uri_value) )->elements;
	
	if ($STRICT_APPROVAL) {
		unless ($approved) {
			warn "- skipping test because it isn't approved\n" if ($debug);
			return;
		}
		if ($approved->equal($dawgt->NotClassified)) {
			warn "- skipping test because its approval is dawgt:NotClassified\n" if ($debug);
			return;
		}
	}
	
	my $uri					= URI->new( $queryd->value );
	my $filename			= $uri->file;
	my (undef,$base,undef)	= File::Spec->splitpath( $filename );
	$base					= "file://${base}";
	warn "Loading SPARQL query from file $filename" if ($debug);
	my $sparql				= do { local($/) = undef; open(my $fh, '<', $filename) or do { warn("$!: $filename; " . $test->as_string); return }; binmode($fh, ':utf8'); <$fh> };
	
	my $q			= $sparql;
	$q				=~ s/\s+/ /g;
	if ($debug) {
		warn "### test     : " . $test->as_string . "\n";
		warn "# sparql     : $q\n";
		warn "# data       : " . ($data->as_string =~ s#file://##r) if (blessed($data));
		warn "# graph data : " . ($_->as_string =~ s#file://##r) for (@gdata);
		warn "# result     : " . ($result->as_string =~ s#file://##r);
		warn "# requires   : " . ($req->as_string =~ s#file://##r) if (blessed($req));
	}
	
STRESS:	foreach (1 .. $count) {
		print STDERR "constructing model... " if ($debug);
		my $test_model	= memory_model();
		try {
			if (blessed($data)) {
	# 			warn "*********************** " . Dumper($data->value);
				add_to_model( $test_model, $default_graph, $data->value );
			}
			foreach my $g (@gdata) {
	# 			warn "***** graph: " . $g->as_string . "\n";
				add_to_model( $test_model, $g, $g->value );
			}
		} catch {
			fail($test->as_string);
			record_result(0, $test->as_string);
			print "# died: " . $test->as_string . ": $_\n";
			next STRESS;
		};
		print STDERR "ok\n" if ($debug);
	
		my $resuri		= URI->new( $result->value );
		my $resfilename	= $resuri->file;
	
		TODO: {
			local($TODO)	= (blessed($req)) ? "requires " . $req->as_string : '';
			my $comment;
			my $ok	= try {
				if ($debug) {
					my $q	= $sparql;
					$q		=~ s/([\x{256}-\x{1000}])/'\x{' . sprintf('%x', ord($1)) . '}'/eg;
					warn $q;
				}
				
				my ($actual, $type);
				{
					local($::DEBUG)	= 1;
					print STDERR "getting actual results... " if ($debug);
					($actual, $type)		= get_actual_results( $test_model, $sparql, $base );
					print STDERR "ok\n" if ($debug);
				}
			
				print STDERR "getting expected results... " if ($debug);
				my $expected	= get_expected_results( $resfilename, $type );
				print STDERR "ok\n" if ($debug);
			
			#	warn "comparing results...";
				compare_results( $expected, $actual, $test->as_string, \$comment );
			} catch {
				if (ref($_)) {
					warn $_->message;
					warn $_->stack_trace;
				} else {
					warn $_;
				}
				fail($test->as_string);
				record_result(0, $test->as_string);
			};
			warn $@ if ($@);
			if ($ok) {
			} else {
				print "# failed: " . $test->as_string . "\n";
			}
		}
	}
}


exit;

######################################################################


sub add_to_model {
	my $model	= shift;
	my $graph	= shift;
	my @files	= @_;
	
	foreach my $file (@files) {
		$file	=~ s#^file://##;
		try {
			my $path	= File::Spec->rel2abs($file);
			my $base	= iri("file://$path");
			my $iter;
			open(my $fh, '<:utf8', $file) or die $!;
			my $format;
			$format	= 'turtle' if ($file =~ /[.]ttl$/);
			$format	= 'rdfxml' if ($file =~ /[.]rdf$/);
			$format	= 'ntriples' if ($file =~ /[.]nt$/);
			if ($format) {
				my $format	= ($file =~ /[.]ttl/) ? "turtle" : "rdfxml";
				my $class	= Attean->get_parser($format) || die "Failed to load parser for '$format'";
				my $parser	= $class->new( base => $base ) || die "Failed to construct parser for '$format'";
				$iter	= $parser->parse_iter_from_io($fh);
			} else {
				die "Unrecognized file extension: $file";
			}
			my $quads	= $iter->as_quads($graph);
			$model->add_iter($quads);
		} catch {
			warn "Failed to load $file into model: $_";
			if (ref($_)) {
				warn $_->stack_trace;
			}
		};
	}
}

sub get_actual_results {
	my $model		= shift;
	my $sparql		= shift;
	my $base		= shift;
	my $query		= RDF::Query->new( $sparql, { base => $base, lang => 'sparql11', load_data => 1 } );
	unless ($query) {
		warn RDF::Query->error if ($debug or $PATTERN);
		return;
	}

	my $algebra		= Translator->translate_query($query);
	if ($debug) {
		warn "Walking algebra:\n";
		warn $algebra->as_string;
	}
	
	if ($debug) {
		my $iter	= $model->get_quads;
		warn "Dataset:\n-------------\n";
		while (my $q = $iter->next) {
			say $q->as_string;
		}
		warn "-------------\n";
	}
	
	my $testns	= 'http://example.com/test-results#';
	my $rmodel	= memory_model();

	my $e		= Attean::SimpleQueryEvaluator->new( model => $model, default_graph => $default_graph );
	my $results	= $e->evaluate($algebra, $default_graph);
	my $count	= 1;
	
	$results	= $results->materialize;
	my $item	= $results->peek;
	
	my $type	= 'bindings';
	if ($item) {
		if ($item->does('Attean::API::Triple')) {
			$type	= 'graph';
		} elsif ($item->does('Attean::API::Term')) {
			$type	= 'boolean';
		}
	}
	
	print_results("Actual results", \$results) if ($args{ results });
	return ($results, $type);
	
	# TODO:
	if ($results->is_bindings) {
		return ($results, 'bindings');
	} elsif ($results->is_boolean) {
		$rmodel->add_statement( statement( iri("${testns}result"), iri("${testns}boolean"), literal(($results->get_boolean ? 'true' : 'false'), undef, $xsd->boolean) ) );
		return ($rmodel->get_statements, 'boolean');
	} elsif ($results->is_graph) {
		return ($results, 'graph');
	} else {
		warn "unknown result type: " . Dumper($results);
	}
}

sub print_results {
	my $name	= shift;
	my $results	= shift;
	$$results	= $$results->materialize;
	warn "$name:\n";
	my $count	= 1;
	while (my $r = $$results->next) {
		printf("%3d %s\n", $count++, $r->as_string);
	}
	$$results->reset;
}

sub get_expected_results {
	my $file		= shift;
	my $type		= shift;
	
	my $testns	= RDF::Trine::Namespace->new('http://example.com/test-results#');
	if ($type eq 'graph') {
		my $model	= memory_model();
		add_to_model($model, $default_graph, $file);
		my $results	= $model->get_quads->map(sub { shift->as_triple }, 'Attean::API::Triple');
		print_results("Expected results", \$results) if ($args{ results });
		return $results;
	} elsif ($file =~ /[.](srj|json)/) {
		my $model	= memory_model();
		open(my $fh, '<', $file) or die $!;
		my $parser	= Attean->get_parser('SPARQLJSON')->new();
		my $results	= $parser->parse_iter_from_io($fh)->materialize;
		my $item	= $results->peek;
		if ($item->does('Attean::API::Term')) {
			if ($args{ results }) {
				warn "Expected result: " . $item->as_string . "\n";
			}
			return $results;
		} else {
			print_results("Expected results", \$results) if ($args{ results });
			return $results;
		}
	} elsif ($file =~ /[.]srx/) {
		my $model	= memory_model();
		my $parser	= Attean->get_parser('sparqlxml')->new();
		open(my $fh, '<:encoding(UTF-8)', $file);
		my $results	= $parser->parse_iter_from_io($fh);
		
		print_results("Expected results", \$results) if ($args{ results });
		return $results;
	} elsif ($file =~ /[.]csv/) {
		my $csv	= Text::CSV->new({binary => 1});
		open( my $fh, "<:encoding(utf8)", $file ) or die $!;
		my $header	= $csv->getline($fh);
		my @vars	= @$header;
		my @data;
		while (my $row = $csv->getline($fh)) {
			my %result;
			foreach my $i (0 .. $#vars) {
				my $var		= $vars[$i];
				my $value	= $row->[ $i ];
				# XXX @@ heuristics that won't always work.
				# XXX @@ expected to work on the test suite, though
				if ($value =~ /^_:(\w+)$/) {
					$value	= blank($1);
				} elsif ($value =~ /$RE{URI}/) {
					$value	= iri($value);
				} elsif (defined($value) and length($value)) {
					$value	= literal($value);
				}
				if (ref($value)) {
					$result{ $var }	= $value;
				}
			}
			push(@data, Attean::Result->new( bindings => \%result ));
		}
		my $results	= Attean::ListIterator->new(values => \@data, item_type => 'Attean::API::Result');
		print_results("Expected results", \$results) if ($args{ results });
		return $results;
	} elsif ($file =~ /[.]tsv/) {
		my $parser	= Attean->get_parser('SPARQLTSV')->new();
		open( my $fh, "<:encoding(utf8)", $file ) or die $!;
		my $iter	= $parser->parse_iter_from_io($fh);
		return $iter;
	} elsif ($file =~ /[.](ttl|rdf|nt)/) {
		my $model	= memory_model();
		add_to_model($model, $default_graph, $file);
		my ($res)	= $model->subjects( iri($rdf->type->uri_value), iri($rs->ResultSet->uri_value) )->elements;
		if (my($b) = $model->objects( $res, iri($rs->boolean->uri_value) )->elements) {
			my $bool	= $b->value;
			my $term	= literal(value => $bool, datatype => $xsd->boolean->uri_value);
			if ($args{ results }) {
				warn "Expected result: " . $term->as_string . "\n";
			}
			return Attean::ListIterator->new(values => [$term], item_type => 'Attean::API::Term');
		} else {
			my @vars	= $model->objects( $res, iri($rs->resultVariable->uri_value) )->elements;
			my @sols	= $model->objects( $res, iri($rs->solution->uri_value) )->elements;
			my @names	= map { $_->value } @vars;
			my @bindings;
			foreach my $r (@sols) {
				my %data;
				my @b	= $model->objects( $r, iri($rs->binding->uri_value) );
				foreach my $b (@b) {
					my ($value)	= $model->objects( $b, iri($rs->value->uri_value) );
					my ($var)	= $model->objects( $b, iri($rs->variable->uri_value) );
					$data{ $var->value }	= $value;
				}
				push(@bindings, Attean::Result->new( bindings => \%data ));
			}
			my $results	= Attean::ListIterator->new(values => \@bindings, item_type => 'Attean::API::Result');
			print_results("Expected results", \$results) if ($args{ results });
			return $results;
		}
	} else {
		die "Unrecognized type of expected results: $file";
	}
}

sub compare_results {
	my $expected	= shift->canonicalize->materialize;
	my $actual		= shift->canonicalize->materialize;
	my $test		= shift;
	my $comment		= shift || do { my $foo; \$foo };
	my $TODO		= shift;
	
	if ($actual->does('Attean::API::ResultIterator') or $actual->does('Attean::API::TripleIterator')) {
		my $eqtest	= Attean::BindingEqualityTest->new();
		if ($test =~ /csv0/) {
			# CSV is a lossy format, so strip the languages and datatypes off of literals in the actual results (so that they'll match up with the (lossy) expected results
			my $mapper	= Attean::TermMap->new(mapper => sub {
				my $term	= shift;
				if ($term->does('Attean::API::Literal')) {
					return Attean::Literal->new(value => $term->value);
				}
				return $term;
			});
			$actual	= $actual->map($mapper->binding_mapper);
		}

		my $ok		= ok( $eqtest->equals( $actual, $expected ), $test ) or diag($eqtest->error);
		record_result($ok, $test);
		return $ok;
	} elsif ($actual->does('Attean::API::TermIterator')) {
		my $a	= $actual->next;
		my $e	= $expected->next;
		my $ok		= ok( $a->equals($e), sprintf("$test: %s == %s", $a->as_string, $e->as_string) );
		record_result($ok, $test);
		return $ok;
	} else {
		die "Unexpected result type $actual";
	}
}

{
	my @failures;
	sub record_result {
		my $ok		= shift;
		my $name	= shift;
		unless ($ok) {
			push(@failures, $name);
		}
	}
	END {
		if ($RUN_QUERY_TESTS and scalar(@failures)) {
			@failures	= sort @failures;
			my $msg	= "Failing tests: " . Dumper([@failures]);
			warn $msg;
			unless ($PATTERN) {
				open(my $fh, '>', sprintf('.sparql-test-suite-%d', scalar(time)));
				say $fh join("\n", @failures);
			}
		}
	}
}