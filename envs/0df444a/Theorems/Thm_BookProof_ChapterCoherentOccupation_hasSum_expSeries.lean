-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_expSeries
-- name    : BookProof.ChapterCoherentOccupation.hasSum_expSeries
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:52:48.72516+00:00
-- url     : https://prove2.me/theorems/89dcacdb-ad23-4107-90ea-019881c4b037
-- title:
--   `BookProof.ChapterCoherentOccupation.hasSum_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => lam ^ n / (n ! : ℝ)) (Real.exp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.hasSum_expSeries` (lam : ℝ) : HasSum (fun n : ℕ => lam ^ n / (n ! : ℝ)) (Real.exp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.hasSum_expSeries`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.hasSum_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.hasSum_expSeries (lam : ℝ) :
    HasSum (fun n : ℕ => lam ^ n / (n ! : ℝ)) (Real.exp lam) := by sorry
