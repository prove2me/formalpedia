-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_approximate_proof_error
-- name    : BookProof.ChapterStatementOperator.approximate_proof_error
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:45:18.972975+00:00
-- url     : https://prove2.me/theorems/ac4fae14-8b5a-4e9b-aa2f-052a026af13f
-- title:
--   `BookProof.ChapterStatementOperator.approximate_proof_error` (S : ModelStatement H) (A : H →L[ℂ] H) (ε : ℝ) (hA : ‖A - S.op‖ ≤ ε) (ψ : H) : |RCLike.re (inner ℂ ψ (A ψ)) - S.truthVa
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.approximate_proof_error` (S : ModelStatement H) (A : H →L[ℂ] H) (ε : ℝ) (hA : ‖A - S.op‖ ≤ ε) (ψ : H) : |RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ| ≤ ε * ‖ψ‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.approximate_proof_error`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.approximate_proof_error
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.approximate_proof_error (S : ModelStatement H) (A : H →L[ℂ] H) (ε : ℝ)
    (hA : ‖A - S.op‖ ≤ ε) (ψ : H) :
    |RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ| ≤ ε * ‖ψ‖ ^ 2 := by sorry
