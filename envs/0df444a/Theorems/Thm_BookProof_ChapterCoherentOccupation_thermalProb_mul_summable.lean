-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalProb_mul_summable
-- name    : BookProof.ChapterCoherentOccupation.thermalProb_mul_summable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:35.364151+00:00
-- url     : https://prove2.me/theorems/0d350dea-6bd7-4c94-b5ee-25b89b98b679
-- title:
--   `BookProof.ChapterCoherentOccupation.thermalProb_mul_summable` {nbar : ℝ} (h : 0 ≤ nbar) : Summable (fun n : ℕ => (n : ℝ) * thermalProb nbar n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.thermalProb_mul_summable` {nbar : ℝ} (h : 0 ≤ nbar) : Summable (fun n : ℕ => (n : ℝ) * thermalProb nbar n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.thermalProb_mul_summable`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.thermalProb_mul_summable
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.thermalProb_mul_summable {nbar : ℝ} (h : 0 ≤ nbar) :
    Summable (fun n : ℕ => (n : ℝ) * thermalProb nbar n) := by sorry
