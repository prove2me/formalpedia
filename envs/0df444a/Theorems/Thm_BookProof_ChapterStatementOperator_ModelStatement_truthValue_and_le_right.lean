-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_truthValue_and_le_right
-- name    : BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:50:59.596911+00:00
-- url     : https://prove2.me/theorems/a566cb2e-2509-43b9-a7bc-9b1d094b6781
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right` (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) : (S.and T hcomm).truthValue ψ ≤ T.truthV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right` (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) : (S.and T hcomm).truthValue ψ ≤ T.truthValue ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right
import Mathlib
import Definitions.Def_ChapterStatementOperator
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right (S T : ModelStatement H)
    (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).truthValue ψ ≤ T.truthValue ψ := by sorry
