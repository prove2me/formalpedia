-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_hasSum_mean
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:22.330178+00:00
-- url     : https://prove2.me/theorems/33e5f4e9-66e0-4d66-9935-6c5c0351d80b
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * coherentOccupation lam n) lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * coherentOccupation lam n) lam
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * coherentOccupation lam n) lam := by sorry
