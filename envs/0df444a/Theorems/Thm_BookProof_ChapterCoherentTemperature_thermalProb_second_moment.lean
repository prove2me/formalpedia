-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_second_moment
-- name    : BookProof.ChapterCoherentTemperature.thermalProb_second_moment
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:10:34.622157+00:00
-- url     : https://prove2.me/theorems/8e50330b-107a-44d1-8e6a-537e5060e848
-- title:
--   `BookProof.ChapterCoherentTemperature.thermalProb_second_moment` (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n = 2 * nbar ^ 2 + nbar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentTemperature`.
--
--   `BookProof.ChapterCoherentTemperature.thermalProb_second_moment` (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n = 2 * nbar ^ 2 + nbar
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentTemperature.thermalProb_second_moment`.

-- Generated from ChapterCoherentTemperature.lean — theorem BookProof.ChapterCoherentTemperature.thermalProb_second_moment
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature


noncomputable section




variable {nbar : ℝ}

theorem BookProof.ChapterCoherentTemperature.thermalProb_second_moment (h : 0 ≤ nbar) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n = 2 * nbar ^ 2 + nbar := by sorry
