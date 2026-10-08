-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_band_refinement_rational
-- name    : BookProof.ChapterH8.sirk_band_refinement_rational
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:32:36.211408+00:00
-- url     : https://prove2.me/theorems/f855b0e4-9f29-44b3-8774-6eda47c09bf9
-- title:
--   `BookProof.ChapterH8.sirk_band_refinement_rational` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X qX qXinv : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G) (p...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.sirk_band_refinement_rational` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X qX qXinv : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G) (p : Polynomial ℂ) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y) (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y) (hqn : ∀ x : F, ∃ y : F, qX (Vn x) = Vn y) (hqm : ∀ x : G, ∃ y : G, qX (Vm x) = Vm y) (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E) (hqBrn : (compress Vn qX).comp qBninv = ContinuousLinearMap.id ℂ F) (hqBrm : (compress Vm qX).comp qBminv = ContinuousLinearMap.id ℂ G) (v : E) (hv : Vn ((adjoint Vn) v) = v) : Vm ((Polynomial.aeval (compress Vm X) p) (qBminv ((adjoint Vm) v))) = Vn ((Polynomial.aeval (compress Vn X) p) (qBninv ((adjoint Vn) v)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.sirk_band_refinement_rational`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_band_refinement_rational
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

theorem BookProof.ChapterH8.sirk_band_refinement_rational (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X qX qXinv : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G)
    (p : Polynomial ℂ) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (hqn : ∀ x : F, ∃ y : F, qX (Vn x) = Vn y)
    (hqm : ∀ x : G, ∃ y : G, qX (Vm x) = Vm y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBrn : (compress Vn qX).comp qBninv = ContinuousLinearMap.id ℂ F)
    (hqBrm : (compress Vm qX).comp qBminv = ContinuousLinearMap.id ℂ G)
    (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm ((Polynomial.aeval (compress Vm X) p) (qBminv ((adjoint Vm) v)))
      = Vn ((Polynomial.aeval (compress Vn X) p) (qBninv ((adjoint Vn) v))) := by sorry
