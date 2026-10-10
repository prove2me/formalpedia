-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityAccuracy_fundamental
-- name    : ActuarialValuation.exposureCredibilityAccuracy_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:19:36.010063+00:00
-- url     : https://prove2.me/theorems/18631aa0-ea65-4b76-96d8-20ba04504c26
-- title:
--   Exposure increases credibility and weakly improves optimal accuracy
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The capstone reconciles exposure-driven increases in credibility with the monotone decline of minimum expected squared error, including the zero heterogeneity boundary. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   Z(P_1)\le Z(P_2),\quad G(P_1,P_2)\ge0,\quad R_{\min}(P_2)\le R_{\min}(P_1)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityAccuracy_fundamental is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityMinError
import Definitions.Def_actuarial_exposureCredibilityGain

namespace ActuarialValuation

theorem exposureCredibilityAccuracy_fundamental
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  (exposureCredibilityWeight EPV VHM P₁ ≤
    exposureCredibilityWeight EPV VHM P₂) ∧
  (0 ≤ exposureCredibilityGain EPV VHM P₁ P₂) ∧
  (exposureCredibilityMinError EPV VHM P₂ ≤
    exposureCredibilityMinError EPV VHM P₁) := by sorry

end ActuarialValuation
