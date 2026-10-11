-- Prove2me | Theorems.Thm_BookProof_ChapterStatementOperator_ModelStatement_truthValue_mem_unitInterval
-- name    : BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:44:50.544954+00:00
-- url     : https://prove2.me/theorems/fad120bb-463c-4498-8370-523354348307
-- title:
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval` (hψ : ‖ψ‖ = 1) : S.truthValue ψ ∈ Set.Icc (0 : ℝ) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStatementOperator`.
--
--   `BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval` (hψ : ‖ψ‖ = 1) : S.truthValue ψ ∈ Set.Icc (0 : ℝ) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval`.

-- Generated from ChapterStatementOperator.lean — theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator



open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : ModelStatement H) (ψ : H)

theorem BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval (hψ : ‖ψ‖ = 1) :
    S.truthValue ψ ∈ Set.Icc (0 : ℝ) 1 := by sorry
