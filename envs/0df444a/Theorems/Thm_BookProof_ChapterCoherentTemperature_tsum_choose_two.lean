-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentTemperature_tsum_choose_two
-- name    : BookProof.ChapterCoherentTemperature.tsum_choose_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:10:29.277019+00:00
-- url     : https://prove2.me/theorems/e8d65851-9d08-47b6-99da-2b95576e6073
-- title:
--   `BookProof.ChapterCoherentTemperature.tsum_choose_two` (h : 0 ≤ nbar) : ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * thermalRatio nbar ^ n = 1 / (1 - thermalRatio nbar) ^ 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentTemperature`.
--
--   `BookProof.ChapterCoherentTemperature.tsum_choose_two` (h : 0 ≤ nbar) : ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * thermalRatio nbar ^ n = 1 / (1 - thermalRatio nbar) ^ 3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentTemperature.tsum_choose_two`.

-- Generated from ChapterCoherentTemperature.lean — theorem BookProof.ChapterCoherentTemperature.tsum_choose_two
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature


noncomputable section




variable {nbar : ℝ}

theorem BookProof.ChapterCoherentTemperature.tsum_choose_two (h : 0 ≤ nbar) :
    ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * thermalRatio nbar ^ n
      = 1 / (1 - thermalRatio nbar) ^ 3 := by sorry
