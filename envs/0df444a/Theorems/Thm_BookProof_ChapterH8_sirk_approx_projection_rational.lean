-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_approx_projection_rational
-- name    : BookProof.ChapterH8.sirk_approx_projection_rational
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:35:29.933626+00:00
-- url     : https://prove2.me/theorems/d6aae3c9-dfe4-48df-87cc-70577359e9d9
-- title:
--   `BookProof.ChapterH8.sirk_approx_projection_rational` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X qX : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G) (p :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.sirk_approx_projection_rational` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X qX : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G) (p : Polynomial ℂ) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y) (hqadj : ∀ x : F, ∃ y : F, (adjoint qX) (Vn x) = Vn y) (hqBnl : qBninv.comp (compress Vn qX) = ContinuousLinearMap.id ℂ F) (hqBmr : (compress Vm qX).comp qBminv = ContinuousLinearMap.id ℂ G) (v : E) : Vn ((adjoint Vn) (Vm ((Polynomial.aeval (compress Vm X) p) (qBminv ((adjoint Vm) v))))) = Vn ((Polynomial.aeval (compress Vn X) p) (qBninv ((adjoint Vn) v)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.sirk_approx_projection_rational`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_approx_projection_rational
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

theorem BookProof.ChapterH8.sirk_approx_projection_rational (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X qX : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G) (p : Polynomial ℂ)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y)
    (hqadj : ∀ x : F, ∃ y : F, (adjoint qX) (Vn x) = Vn y)
    (hqBnl : qBninv.comp (compress Vn qX) = ContinuousLinearMap.id ℂ F)
    (hqBmr : (compress Vm qX).comp qBminv = ContinuousLinearMap.id ℂ G)
    (v : E) :
    Vn ((adjoint Vn) (Vm ((Polynomial.aeval (compress Vm X) p) (qBminv ((adjoint Vm) v)))))
      = Vn ((Polynomial.aeval (compress Vn X) p) (qBninv ((adjoint Vn) v))) := by sorry
