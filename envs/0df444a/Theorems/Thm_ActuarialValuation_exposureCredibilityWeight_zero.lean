-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityWeight_zero
-- name    : ActuarialValuation.exposureCredibilityWeight_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:35.117995+00:00
-- url     : https://prove2.me/theorems/ce4e6778-03db-4c99-87a3-fccf0b2abfb9
-- title:
--   Zero exposure implies zero weight on risk experience
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. Without any exposure, the experience credibility weight must be zero, provided the process variance is strictly positive. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \mathrm{EPV}>0\Longrightarrow Z(0)=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityWeight_zero is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

theorem exposureCredibilityWeight_zero
  (EPV VHM : ℝ) (hE : 0 < EPV) :
  exposureCredibilityWeight EPV VHM 0 = 0 := by sorry

end ActuarialValuation
