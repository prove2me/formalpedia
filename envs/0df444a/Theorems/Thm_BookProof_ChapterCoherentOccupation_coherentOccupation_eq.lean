-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:53:46.880347+00:00
-- url     : https://prove2.me/theorems/3424648d-70f4-4c1e-9f24-4410cbab7ab1
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_eq` (lam : ℝ) (n : ℕ) : coherentOccupation lam n = Real.exp (-lam) * (lam ^ n / (n ! : ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_eq` (lam : ℝ) (n : ℕ) : coherentOccupation lam n = Real.exp (-lam) * (lam ^ n / (n ! : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_eq`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_eq
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_eq (lam : ℝ) (n : ℕ) :
    coherentOccupation lam n = Real.exp (-lam) * (lam ^ n / (n ! : ℝ)) := by sorry
