-- Prove2me | Theorems.Thm_BookProof_ChapterH9_ritz_mem_numRange_compress
-- name    : BookProof.ChapterH9.ritz_mem_numRange_compress
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:57.752019+00:00
-- url     : https://prove2.me/theorems/2dae9148-2baa-4050-a16a-73ca1ec10082
-- title:
--   The Lean 4 theorem `ritz_mem_numRange_compress` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritz_mem_numRange_compress` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.ritz_mem_numRange_compress
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.ritz_mem_numRange_compress (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖)
    {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress Vn X y = lam • y) :
    lam ∈ numRange (compress Vm X) := by sorry
