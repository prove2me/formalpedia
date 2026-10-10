-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_truthValue_not
-- name    : BookProof.ChapterStatementOperator.ModelStatement.truthValue_not
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:50:27.634009+00:00
-- url     : https://prove2.me/theorems/b596b4f8-46bc-45a2-bd3d-c7b4501b261b
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_not` : S.not.truthValue ψ = ‖ψ‖ ^ 2 - S.truthValue ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_not` : S.not.truthValue ψ = ‖ψ‖ ^ 2 - S.truthValue ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.truthValue_not`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_not
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_not : S.not.truthValue ψ = ‖ψ‖ ^ 2 - S.truthValue ψ := by sorry
