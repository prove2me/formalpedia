-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_halfUncertain_not_idempotent
-- name    : BookProof.ChapterStatementOperator.halfUncertain_not_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:51:33.543618+00:00
-- url     : https://prove2.me/theorems/6116aeea-3d61-4501-998f-21ffc84a4e2e
-- title:
--   `BookProof.ChapterStatementOperator.halfUncertain_not_idempotent` (h : ∃ ψ : H, ψ ≠ 0) : ¬ ((halfUncertain (H := H)).op ∘L (halfUncertain (H := H)).op = (halfUncertain (H := H)).op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.halfUncertain_not_idempotent` (h : ∃ ψ : H, ψ ≠ 0) : ¬ ((halfUncertain (H := H)).op ∘L (halfUncertain (H := H)).op = (halfUncertain (H := H)).op)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.halfUncertain_not_idempotent`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.halfUncertain_not_idempotent
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.halfUncertain_not_idempotent (h : ∃ ψ : H, ψ ≠ 0) :
    ¬ ((halfUncertain (H := H)).op ∘L (halfUncertain (H := H)).op
        = (halfUncertain (H := H)).op) := by sorry
