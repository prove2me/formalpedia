-- Prove2me | Theorems.Thm_CatalyticMatching_General_matching_size_in_clp
-- name    : CatalyticMatching.General.matching_size_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:11.295199+00:00
-- url     : https://prove2.me/theorems/d2f1720e-64bf-45b8-87ab-5e9071746c80
-- title:
--   Theorem 3.8 — maximum matching cardinality in CLP
-- statement:
--   For every finite simple graph $G$, one uniform deterministic catalytic machine computes
--
--   $$\operatorname{enc}(G)\longmapsto\operatorname{bin}(\nu(G))\quad\text{in CLP}.$$
--
--   The same machine and resource constants apply to all graph sizes and every arbitrary initial catalyst, which is restored completely. Time is polynomial and ordinary workspace logarithmic in total input length. As a function, the cardinality output is independent of the catalyst.
--
--   Differences from the source:
--   - encoding: CL or CLP in the total binary input length → one finite binary transition table, explicit input domain, uniform C and polynomial p, logBudget(L)=floor(log₂(L+2))+1, and for CLP a uniform time exponent k; reason: standard tape and positive-logarithm conventions change bounds only by fixed factors; all inputs, outputs, intermediate work cells and complete catalyst restoration are charged
--   - encoding: explicitly encoded graphs, assignments and output witnesses → unary vertex header plus n² adjacency bits, symmetric n² matching bits, framed reduced binary rationals and row-major matrix outputs; reason: polynomially equivalent explicit encodings preserve all finite inputs and allow the witness to depend on the initial catalyst
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Theorem 3.8, printed p.13 = PDF p.13

import Definitions.Def_CatalyticMatching_General_SearchRelations

namespace CatalyticMatching.General

/-- Theorem 3.8 p.13, proof pp.13--16. One machine computes the function ν(G) for every catalyst. -/
theorem matching_size_in_clp : InCLP graphDomain matchingSizeRelation := by sorry

end CatalyticMatching.General
