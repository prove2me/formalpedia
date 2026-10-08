-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalTemperature_eq_mean_add_half
-- name    : BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:11:02.368419+00:00
-- url     : https://prove2.me/theorems/83adbf45-7291-4c24-b612-750c69dab429
-- title:
--   `BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half` (h : 0 ≤ nbar) : thermalTemperature nbar = (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) + 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentTemperature`.
--
--   `BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half` (h : 0 ≤ nbar) : thermalTemperature nbar = (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) + 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half`.

-- Generated from ChapterCoherentTemperature.lean — theorem BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature


noncomputable section




variable {nbar : ℝ}

theorem BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half (h : 0 ≤ nbar) :
    thermalTemperature nbar = (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) + 1 / 2 := by sorry
