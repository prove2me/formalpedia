-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_mean
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_mean
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:26.295079+00:00
-- url     : https://prove2.me/theorems/50453ee2-70b1-46ce-bc30-81de77f31aef
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_mean` (lam : ℝ) : ∑' n : ℕ, (n : ℝ) * coherentOccupation lam n = lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_mean` (lam : ℝ) : ∑' n : ℕ, (n : ℝ) * coherentOccupation lam n = lam
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_mean`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_mean
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_mean (lam : ℝ) :
    ∑' n : ℕ, (n : ℝ) * coherentOccupation lam n = lam := by sorry
