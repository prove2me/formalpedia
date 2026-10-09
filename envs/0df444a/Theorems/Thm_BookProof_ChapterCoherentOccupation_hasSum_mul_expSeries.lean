-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_mul_expSeries
-- name    : BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:53:42.511357+00:00
-- url     : https://prove2.me/theorems/9fd474c3-d194-4fc7-aea0-960ae9d611bd
-- title:
--   `BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * (lam ^ n / (n ! : ℝ))) (lam * Real.exp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * (lam ^ n / (n ! : ℝ))) (lam * Real.exp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (lam ^ n / (n ! : ℝ))) (lam * Real.exp lam) := by sorry
