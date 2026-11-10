-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_aps_in_counting_hierarchy
-- name    : ApproxPolySatCH.Main.aps_in_counting_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:38.584646+00:00
-- url     : https://prove2.me/theorems/633879da-55ea-4c2f-a22a-ae9c4845d20e
-- title:
--   Theorem 1 — APS over rationals and finite fields lies in CH
-- statement:
--   For the rational coefficient field and for every finite field $k=\mathbb F_p[U]/(\mu)$ with p prime and mu monic irreducible of positive degree, the actual approximate polynomial satisfiability problem lies in the counting hierarchy:
--   $$\mathrm{APS}_k\in CH.$$
--   For a polynomial map $f:K^n\to K^m$, where $K=\overline k$, acceptance means $0\in\overline{f(K^n)}^{\mathrm{Zar}}$. A tagged language includes sparse binary-exponent lists, dense coefficient arrays and division-free shared arithmetic DAGs. Rational coefficients use binary integer pairs with nonzero denominator; finite-field coefficients use their power basis. There is no bound on dimension, degree, characteristic or coefficient size, and empty and constant systems are included.
--
--   For each fixed k, the hierarchy level, finite transition tables and polynomial clocks are chosen before every encoded input. The base level is P and successive levels are strict-majority PP with an oracle in the preceding level. No oracle for the target algebraic problem is assumed.
--
--   This is Theorem 1 at its full field and input-representation scope.
--
--   Differences from the source:
--   - encoding: APS for every rational or finite field, with the equivalent sparse, dense and circuit input conventions. → For each fixed coefficient presentation, one tagged union of the three actual encoded APS languages belongs to finite-machine CH.; reason: Tags form a finite union of the equivalent versions, and all field, machine, level and clock choices precede every input; no additional field regime is asserted.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Theorem 1, p.7 (PDF p.7), proof p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=7

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem aps_in_counting_hierarchy : ∀ k : CoefficientField, InCH (APSLanguage k) := by sorry

end ApproxPolySatCH.Main
