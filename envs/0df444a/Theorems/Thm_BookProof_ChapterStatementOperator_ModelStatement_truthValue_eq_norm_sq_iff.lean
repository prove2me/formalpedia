-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_truthValue_eq_norm_sq_iff
-- name    : BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:45:49.368098+00:00
-- url     : https://prove2.me/theorems/bb3d7384-0a80-4b11-b2cb-e39b4cb64653
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff` : S.truthValue ψ = ‖ψ‖ ^ 2 ↔ S.op ψ = ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff` : S.truthValue ψ = ‖ψ‖ ^ 2 ↔ S.op ψ = ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff : S.truthValue ψ = ‖ψ‖ ^ 2 ↔ S.op ψ = ψ := by sorry
