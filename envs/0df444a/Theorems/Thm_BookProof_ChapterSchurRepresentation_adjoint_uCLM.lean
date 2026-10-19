-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_adjoint_uCLM
-- name    : BookProof.ChapterSchurRepresentation.adjoint_uCLM
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:49.677751+00:00
-- url     : https://prove2.me/theorems/856591e3-c06e-4afd-a5cc-74a942388a20
-- title:
--   `BookProof.ChapterSchurRepresentation.adjoint_uCLM` (f : V ≃ₗᵢ[ℂ] V) : ContinuousLinearMap.adjoint (uCLM f) = uCLM f.symm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.adjoint_uCLM` (f : V ≃ₗᵢ[ℂ] V) : ContinuousLinearMap.adjoint (uCLM f) = uCLM f.symm
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.adjoint_uCLM`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.adjoint_uCLM
import Definitions.Def_ChapterA
import Definitions.Def_ChapterSchurIrreducible
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
open BookProof.ChapterSchurRepresentation


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurRepresentation.adjoint_uCLM (f : V ≃ₗᵢ[ℂ] V) :
    ContinuousLinearMap.adjoint (uCLM f) = uCLM f.symm := by sorry
