-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_band_refinement
-- name    : BookProof.ChapterH8.sirk_band_refinement
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:32:21.812143+00:00
-- url     : https://prove2.me/theorems/d3f4022b-fe28-4b30-9eb1-a6be42bfad9f
-- title:
--   `BookProof.ChapterH8.sirk_band_refinement` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.sirk_band_refinement` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y) (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y) (k : ℕ) (v : E) (hv : Vn ((adjoint Vn) v) = v) : Vm (((compress Vm X) ^ k) ((adjoint Vm) v)) = Vn (((compress Vn X) ^ k) ((adjoint Vn) v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.sirk_band_refinement`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_band_refinement
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

theorem BookProof.ChapterH8.sirk_band_refinement (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (k : ℕ) (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm (((compress Vm X) ^ k) ((adjoint Vm) v)) = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by sorry
