-- Prove2me | Theorems.Thm_BookProof_ChapterA_rImagCx_commutes
-- name    : BookProof.ChapterA.rImagCx_commutes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:03.151994+00:00
-- url     : https://prove2.me/theorems/6fc7ba28-6a90-4f47-9d68-ac2d0d849e75
-- title:
--   `BookProof.ChapterA.rImagCx_commutes` {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) {m : W →L[ℝ] W} (hm : m ∈ M.ops) (x : Cx W) : rImagCx J (Cx.cxMap m x) = Cx.cxMap m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.rImagCx_commutes` {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) {m : W →L[ℝ] W} (hm : m ∈ M.ops) (x : Cx W) : rImagCx J (Cx.cxMap m x) = Cx.cxMap m (rImagCx J x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.rImagCx_commutes`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.rImagCx_commutes
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

theorem BookProof.ChapterA.rImagCx_commutes {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J)
    {m : W →L[ℝ] W} (hm : m ∈ M.ops) (x : Cx W) :
    rImagCx J (Cx.cxMap m x) = Cx.cxMap m (rImagCx J x) := by sorry
