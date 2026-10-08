-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_mean
-- name    : BookProof.ChapterCoherentTemperature.thermalProb_mean
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:10:21.374235+00:00
-- url     : https://prove2.me/theorems/0f0d00ec-b47b-4c7a-8236-0ee5d6662ee5
-- title:
--   `BookProof.ChapterCoherentTemperature.thermalProb_mean` (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) * thermalProb nbar n = nbar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentTemperature`.
--
--   `BookProof.ChapterCoherentTemperature.thermalProb_mean` (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) * thermalProb nbar n = nbar
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentTemperature.thermalProb_mean`.

-- Generated from ChapterCoherentTemperature.lean — theorem BookProof.ChapterCoherentTemperature.thermalProb_mean
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature


noncomputable section




variable {nbar : ℝ}

theorem BookProof.ChapterCoherentTemperature.thermalProb_mean (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) * thermalProb nbar n = nbar := by sorry
