-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_approx_projection
-- name    : BookProof.ChapterH8.sirk_approx_projection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:34:23.825329+00:00
-- url     : https://prove2.me/theorems/8026137e-1dfe-408b-bf09-5e91e5ecf0d6
-- title:
--   `BookProof.ChapterH8.sirk_approx_projection` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearM
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.sirk_approx_projection` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y) (k : ℕ) (v : E) : Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v)))) = Vn (((compress Vn X) ^ k) ((adjoint Vn) v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.sirk_approx_projection`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_approx_projection
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open ContinuousLinearMap

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterH8.sirk_approx_projection (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y)
    (k : ℕ) (v : E) :
    Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v))))
      = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by sorry
