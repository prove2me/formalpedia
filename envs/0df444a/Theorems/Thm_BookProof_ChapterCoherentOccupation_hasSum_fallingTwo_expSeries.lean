-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_fallingTwo_expSeries
-- name    : BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:03.672289+00:00
-- url     : https://prove2.me/theorems/b2db69f9-5b7c-4b8b-a624-71c11123e89d
-- title:
--   `BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (lam ^ n / (n ! : ℝ))) (lam ^ 2 * Real.exp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (lam ^ n / (n ! : ℝ))) (lam ^ 2 * Real.exp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (lam ^ n / (n ! : ℝ)))
      (lam ^ 2 * Real.exp lam) := by sorry
