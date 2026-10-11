-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_undecidable_iff
-- name    : BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:44:58.911905+00:00
-- url     : https://prove2.me/theorems/2eab9fb4-7020-444a-b8fd-9227f8896d11
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff` : S.Undecidable ↔ (∃ a : H, a ≠ 0 ∧ S.op a = a) ∧ (∃ b : H, b ≠ 0 ∧ S.op b = 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff` : S.Undecidable ↔ (∃ a : H, a ≠ 0 ∧ S.op a = a) ∧ (∃ b : H, b ≠ 0 ∧ S.op b = 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff :
    S.Undecidable ↔ (∃ a : H, a ≠ 0 ∧ S.op a = a) ∧ (∃ b : H, b ≠ 0 ∧ S.op b = 0) := by sorry
