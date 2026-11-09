-- Prove2me | Theorems.Thm_CatalyticMatching_General_perfect_matching_in_clp
-- name    : CatalyticMatching.General.perfect_matching_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:11.13427+00:00
-- url     : https://prove2.me/theorems/55cb2cf3-53ad-43f2-83f7-37252e72c75e
-- title:
--   Lemma 3.11 — perfect matching construction in CLP
-- statement:
--   Given any finite simple undirected graph $G$ that contains a perfect matching, a uniform deterministic catalytic procedure constructs
--
--   $$M\subseteq E(G)\quad\text{such that every vertex is incident to exactly one edge of }M,\quad\text{in CLP}.$$
--
--   This graph promise is the entire input restriction. The procedure receives no full-rank evaluation, isolating weights or subroutine oracle. The machine restores every initial catalyst and satisfies simultaneous polynomial time, logarithmic ordinary work and polynomial catalyst bounds. Its valid matching output may depend on the catalyst.
--
--   Differences from the source:
--   - encoding: CL or CLP in the total binary input length → one finite binary transition table, explicit input domain, uniform C and polynomial p, logBudget(L)=floor(log₂(L+2))+1, and for CLP a uniform time exponent k; reason: standard tape and positive-logarithm conventions change bounds only by fixed factors; all inputs, outputs, intermediate work cells and complete catalyst restoration are charged
--   - encoding: explicitly encoded graphs, assignments and output witnesses → unary vertex header plus n² adjacency bits, symmetric n² matching bits, framed reduced binary rationals and row-major matrix outputs; reason: polynomially equivalent explicit encodings preserve all finite inputs and allow the witness to depend on the initial catalyst
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 3.11, printed p.20 = PDF p.20

import Definitions.Def_CatalyticMatching_General_SearchRelations

namespace CatalyticMatching.General

/-- Lemma 3.11 p.20, proof pp.20--21. The only promise is existence of a perfect matching; no full-rank evaluation is supplied. -/
theorem perfect_matching_in_clp : InCLP perfectGraphDomain perfectMatchingRelation := by sorry

end CatalyticMatching.General
