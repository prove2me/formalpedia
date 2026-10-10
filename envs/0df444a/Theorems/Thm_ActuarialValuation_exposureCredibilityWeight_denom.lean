-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityWeight_denom
-- name    : ActuarialValuation.exposureCredibilityWeight_denom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:47:13.758974+00:00
-- url     : https://prove2.me/theorems/4bb120d6-e791-4542-9355-3c932f2f7132
-- title:
--   Credibility weight satisfies its rational defining identity
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The defining rational formula is recovered without division, using the fact that its denominator is strictly positive. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   (P\,\mathrm{VHM}+\mathrm{EPV})Z(P)=P\,\mathrm{VHM}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityWeight_denom is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

theorem exposureCredibilityWeight_denom
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  (P * VHM + EPV) * exposureCredibilityWeight EPV VHM P =
    P * VHM := by sorry

end ActuarialValuation
