-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityGain_nonneg
-- name    : ActuarialValuation.exposureCredibilityGain_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:18:32.742959+00:00
-- url     : https://prove2.me/theorems/2cb584b3-6df4-4634-bd94-607b11d1c68b
-- title:
--   Additional exposure cannot create negative credibility gain
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The change in experience credibility after additional exposure is necessarily nonnegative when the variance model is actuarially admissible. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   P_1\le P_2\Longrightarrow G(P_1,P_2)\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityGain_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityGain

namespace ActuarialValuation

theorem exposureCredibilityGain_nonneg
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  0 ≤ exposureCredibilityGain EPV VHM P₁ P₂ := by sorry

end ActuarialValuation
