-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityWeight_mono
-- name    : ActuarialValuation.exposureCredibilityWeight_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:18:17.85519+00:00
-- url     : https://prove2.me/theorems/af3ce55b-482a-4ce8-ba80-4d0f3af9364a
-- title:
--   Credibility weight weakly increases with exposure
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. More accumulated exposure provides at least as much statistical evidence and must not reduce Bühlmann–Straub credibility. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   0\le P_1\le P_2\Longrightarrow Z(P_1)\le Z(P_2)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityWeight_mono is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

theorem exposureCredibilityWeight_mono
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  exposureCredibilityWeight EPV VHM P₁ ≤
    exposureCredibilityWeight EPV VHM P₂ := by sorry

end ActuarialValuation
