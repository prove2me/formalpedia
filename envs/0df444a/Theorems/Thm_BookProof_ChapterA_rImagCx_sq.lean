-- Prove2me | Theorems.Thm_BookProof_ChapterA_rImagCx_sq
-- name    : BookProof.ChapterA.rImagCx_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:34:55.504327+00:00
-- url     : https://prove2.me/theorems/7c1e0537-25c7-4506-8d2e-0e2b493f8ceb
-- title:
--   `BookProof.ChapterA.rImagCx_sq` {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) (x : Cx W) : rImagCx J (rImagCx J x) = -x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.rImagCx_sq` {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) (x : Cx W) : rImagCx J (rImagCx J x) = -x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.rImagCx_sq`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.rImagCx_sq
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.AntiUnitary
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.rImagCx_sq {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) (x : Cx W) :
    rImagCx J (rImagCx J x) = -x := by sorry
