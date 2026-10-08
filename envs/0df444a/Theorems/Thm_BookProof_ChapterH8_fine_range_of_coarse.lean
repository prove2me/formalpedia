-- Prove2me | Theorems.Thm_BookProof_ChapterH8_fine_range_of_coarse
-- name    : BookProof.ChapterH8.fine_range_of_coarse
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:30:26.419158+00:00
-- url     : https://prove2.me/theorems/5a1073af-1549-454b-9c35-25bbb7621921
-- title:
--   `BookProof.ChapterH8.fine_range_of_coarse` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (v : E)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.fine_range_of_coarse` (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (hJ : Vn = Vm.comp J) (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) (v : E) (hv : Vn ((adjoint Vn) v) = v) : Vm ((adjoint Vm) v) = v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.fine_range_of_coarse`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.fine_range_of_coarse
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
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

theorem BookProof.ChapterH8.fine_range_of_coarse (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm ((adjoint Vm) v) = v := by sorry
