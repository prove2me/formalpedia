-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_coefficient_zero_in_ch
-- name    : ApproxPolySatCH.Main.coefficient_zero_in_ch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:10.610145+00:00
-- url     : https://prove2.me/theorems/29d419f1-ccf7-4145-8be9-cb3278a7c287
-- title:
--   Proposition 13 — Resultant coefficient zero test in CH
-- statement:
--   Given sparse homogeneous forms $P_0,\ldots,P_n\in k[Y_1,\ldots,Y_v][X_0,\ldots,X_n]$ of specified positive X-degrees and a binary exponent tuple beta, exact resultant-coefficient vanishing is in CH:
--   $$\operatorname{coeff}_{Y^\beta}\operatorname{Res}_{X_0,\ldots,X_n}(P_0,\ldots,P_n)=0.$$
--   This holds both over the rationals and for the single finite-field language in which $(p,\mu)$ is supplied as part of the input. The hierarchy level, machine descriptions and polynomial resource bounds in that finite-field language are uniform over every valid field description. Zero forms and an identically zero resultant are allowed.
--
--   This gives the coefficient predicate used in the MRV test.
--
--   Differences from the source:
--   - encoding: Sparse forms of specified positive homogeneous degrees and binary exponent tuple, with the finite field supplied. → Two actual binary-word languages, one rational and one uniform over all supplied finite-field descriptions.; reason: The latter uses one hierarchy level over all p and mu, exactly as the proof requires; zero forms retain their specified degrees.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 13, p.25 (PDF p.25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=25

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem coefficient_zero_in_ch :
    InCH (CoefficientZero .rational) ∧ InCH CoefficientZeroFinite := by sorry

end ApproxPolySatCH.Main
