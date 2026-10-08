-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_variance
-- name    : BookProof.ChapterCoherentTemperature.thermalProb_variance
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:11:10.847875+00:00
-- url     : https://prove2.me/theorems/7aa3df29-69bc-4df0-93ab-e1ba9445adcc
-- title:
--   `BookProof.ChapterCoherentTemperature.thermalProb_variance` (h : 0 ≤ nbar) : (∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n) - (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) ^ 2 = nbar ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentTemperature`.
--
--   `BookProof.ChapterCoherentTemperature.thermalProb_variance` (h : 0 ≤ nbar) : (∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n) - (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) ^ 2 = nbar ^ 2 + nbar
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentTemperature.thermalProb_variance`.

-- Generated from ChapterCoherentTemperature.lean — theorem BookProof.ChapterCoherentTemperature.thermalProb_variance
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature


noncomputable section




variable {nbar : ℝ}

theorem BookProof.ChapterCoherentTemperature.thermalProb_variance (h : 0 ≤ nbar) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n)
      - (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) ^ 2 = nbar ^ 2 + nbar := by sorry
