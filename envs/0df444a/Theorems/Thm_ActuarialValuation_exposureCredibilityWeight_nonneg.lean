-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityWeight_nonneg
-- name    : ActuarialValuation.exposureCredibilityWeight_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:43.9481+00:00
-- url     : https://prove2.me/theorems/a36293f3-3c0b-43d6-8131-214a53772d22
-- title:
--   Credibility weight is nonnegative under actuarial variance conditions
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. Nonnegative exposure and between-risk variance ensure the weight cannot assign a negative proportion to experience. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \mathrm{EPV}>0,\ \mathrm{VHM},P\ge0\Longrightarrow Z(P)\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityWeight_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

theorem exposureCredibilityWeight_nonneg
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  0 ≤ exposureCredibilityWeight EPV VHM P := by sorry

end ActuarialValuation
