-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherent_variance_lt_thermal_variance
-- name    : BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:47.212424+00:00
-- url     : https://prove2.me/theorems/48392a18-29f9-43a2-a97a-ac6c81caa283
-- title:
--   `BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance` {nbar : ℝ} (h : 0 < nbar) : ((∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation nbar n) - (∑' n : ℕ, (n : ℝ) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance` {nbar : ℝ} (h : 0 < nbar) : ((∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation nbar n) - (∑' n : ℕ, (n : ℝ) * coherentOccupation nbar n) ^ 2) < ((∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n) - (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance {nbar : ℝ} (h : 0 < nbar) :
    ((∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation nbar n)
        - (∑' n : ℕ, (n : ℝ) * coherentOccupation nbar n) ^ 2)
      < ((∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n)
        - (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) ^ 2) := by sorry
