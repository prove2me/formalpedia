-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityMinError_mono
-- name    : ActuarialValuation.exposureCredibilityMinError_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:18:54.343727+00:00
-- url     : https://prove2.me/theorems/357bb7c5-aa3c-4d6f-8d3d-2bcd9aa3c2ce
-- title:
--   Minimum prediction error decreases with exposure
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. More observations lower or preserve the best achievable quadratic credibility estimation error for a risk. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   P_1\le P_2\Longrightarrow R_{\min}(P_2)\le R_{\min}(P_1)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityMinError_mono is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityMinError

namespace ActuarialValuation

theorem exposureCredibilityMinError_mono
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  exposureCredibilityMinError EPV VHM P₂ ≤
    exposureCredibilityMinError EPV VHM P₁ := by sorry

end ActuarialValuation
