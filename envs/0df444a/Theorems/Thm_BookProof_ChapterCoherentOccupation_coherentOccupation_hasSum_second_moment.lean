-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_hasSum_second_moment
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:28.505323+00:00
-- url     : https://prove2.me/theorems/8bf0a6e6-9088-42e6-b347-5fac2e899270
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * coherentOccupation lam n) (lam ^ 2 + lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment` (lam : ℝ) : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * coherentOccupation lam n) (lam ^ 2 + lam)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * coherentOccupation lam n) (lam ^ 2 + lam) := by sorry
