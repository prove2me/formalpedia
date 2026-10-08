-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_variance
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_variance
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:54:46.802881+00:00
-- url     : https://prove2.me/theorems/f3468d43-7d1c-49c9-ad8b-455543e5f5e4
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_variance` (lam : ℝ) : (∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n) - (∑' n : ℕ, (n : ℝ) * coherentOccupation lam n) ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_variance` (lam : ℝ) : (∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n) - (∑' n : ℕ, (n : ℝ) * coherentOccupation lam n) ^ 2 = lam
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_variance`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_variance
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_variance (lam : ℝ) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * coherentOccupation lam n)
      - (∑' n : ℕ, (n : ℝ) * coherentOccupation lam n) ^ 2 = lam := by sorry
