-- Prove2me | Theorems.Thm_CatalyticMatching_General_maximum_matching_in_clp
-- name    : CatalyticMatching.General.maximum_matching_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:45.682386+00:00
-- url     : https://prove2.me/theorems/42823743-6d29-4606-88cc-da376476f20b
-- title:
--   Theorem 1.1 / Theorem 3.12 — maximum matching construction in CLP
-- statement:
--   For every finite simple undirected graph $G$, there is one uniform deterministic catalytic machine that constructs a maximum matching:
--
--   $$M\subseteq E(G),\qquad M\text{ is pairwise vertex-disjoint},\qquad |M|=\nu(G),\qquad\text{in CLP}.$$
--
--   One finite program and uniform resource constants work for every graph size and every initial catalyst. Ordinary work uses at most $C(\lfloor\log_2(L+2)\rfloor+1)$ bits, time is at most $C(L+2)^k$, and catalyst length is $p(L)$ for a fixed polynomial with nonnegative integer coefficients; $L$ is total encoded input length. Every catalyst bit is restored at halt after the output is written. The matching may depend on the initial catalyst. Empty, singleton, edgeless, odd-order and nonperfect graphs are all included. No matching cardinality, full-rank evaluation or efficient oracle is assumed. Theorem 3.12 is the expanded proof of this same goal.
--
--   Differences from the source:
--   - encoding: CL or CLP in the total binary input length → one finite binary transition table, explicit input domain, uniform C and polynomial p, logBudget(L)=floor(log₂(L+2))+1, and for CLP a uniform time exponent k; reason: standard tape and positive-logarithm conventions change bounds only by fixed factors; all inputs, outputs, intermediate work cells and complete catalyst restoration are charged
--   - encoding: explicitly encoded graphs, assignments and output witnesses → unary vertex header plus n² adjacency bits, symmetric n² matching bits, framed reduced binary rationals and row-major matrix outputs; reason: polynomially equivalent explicit encodings preserve all finite inputs and allow the witness to depend on the initial catalyst
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Theorem 1.1, printed p.5 = PDF p.5; Theorem 3.12, printed/PDF p.22

import Definitions.Def_CatalyticMatching_General_SearchRelations

namespace CatalyticMatching.General

/-- Theorem 1.1 p.5, proved as Theorem 3.12 p.22. Every finite simple graph, every initial catalyst; no perfect-matching promise. -/
theorem maximum_matching_in_clp : InCLP graphDomain maximumMatchingRelation := by sorry

end CatalyticMatching.General
