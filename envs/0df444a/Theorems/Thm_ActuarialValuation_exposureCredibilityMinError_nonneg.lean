-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityMinError_nonneg
-- name    : ActuarialValuation.exposureCredibilityMinError_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:18:44.031531+00:00
-- url     : https://prove2.me/theorems/17e4e97b-b3e8-4a57-933e-c888f9440785
-- title:
--   Minimum credibility error is nonnegative
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The rational minimum risk is a variance quantity and cannot be negative under nonnegative exposure and between-risk heterogeneity. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   R_{\min}(P)\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityMinError_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityMinError

namespace ActuarialValuation

theorem exposureCredibilityMinError_nonneg
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  0 ≤ exposureCredibilityMinError EPV VHM P := by sorry

end ActuarialValuation
