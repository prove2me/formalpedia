-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_truthValue_eq_zero_iff
-- name    : BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:44:56.529574+00:00
-- url     : https://prove2.me/theorems/10542c2a-99ad-4168-91ce-72be4e970add
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff` : S.truthValue ψ = 0 ↔ S.op ψ = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff` : S.truthValue ψ = 0 ↔ S.op ψ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff : S.truthValue ψ = 0 ↔ S.op ψ = 0 := by sorry
