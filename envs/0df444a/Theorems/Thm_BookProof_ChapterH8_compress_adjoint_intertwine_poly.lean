-- Prove2me | Theorems.Thm_BookProof_ChapterH8_compress_adjoint_intertwine_poly
-- name    : BookProof.ChapterH8.compress_adjoint_intertwine_poly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:34:28.656207+00:00
-- url     : https://prove2.me/theorems/3474f5b4-6002-4057-abcb-e8e71d1ef1da
-- title:
--   `BookProof.ChapterH8.compress_adjoint_intertwine_poly` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = Continu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.compress_adjoint_intertwine_poly` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y) (p : Polynomial ℂ) : (adjoint J).comp (Polynomial.aeval (compress Vm X) p) = (Polynomial.aeval (compress Vn X) p).comp (adjoint J)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.compress_adjoint_intertwine_poly`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.compress_adjoint_intertwine_poly
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

theorem BookProof.ChapterH8.compress_adjoint_intertwine_poly (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y) (p : Polynomial ℂ) :
    (adjoint J).comp (Polynomial.aeval (compress Vm X) p)
      = (Polynomial.aeval (compress Vn X) p).comp (adjoint J) := by sorry
