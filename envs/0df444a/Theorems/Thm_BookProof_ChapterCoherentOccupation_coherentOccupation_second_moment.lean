-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_second_moment
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:31.706425+00:00
-- url     : https://prove2.me/theorems/e8e34aef-c88b-4f70-8c3d-72a9dbc98b83
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment` (lam : ℝ) : ∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n = lam ^ 2 + lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment` (lam : ℝ) : ∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n = lam ^ 2 + lam
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment (lam : ℝ) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n = lam ^ 2 + lam := by sorry
