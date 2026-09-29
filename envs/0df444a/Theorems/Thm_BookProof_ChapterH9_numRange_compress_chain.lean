-- Prove2me | Theorems.Thm_BookProof_ChapterH9_numRange_compress_chain
-- name    : BookProof.ChapterH9.numRange_compress_chain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:45.623134+00:00
-- url     : https://prove2.me/theorems/77345b12-6c32-4830-8c72-b35d238bd16e
-- title:
--   The Lean 4 theorem `numRange_compress_chain` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `numRange_compress_chain` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.numRange_compress_chain
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

theorem BookProof.ChapterH9.numRange_compress_chain (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖)
    (hViso : ∀ x : G, ‖Vm x‖ = ‖x‖) :
    numRange (compress Vn X) ⊆ numRange (compress Vm X)
      ∧ numRange (compress Vm X) ⊆ numRange X := by sorry
