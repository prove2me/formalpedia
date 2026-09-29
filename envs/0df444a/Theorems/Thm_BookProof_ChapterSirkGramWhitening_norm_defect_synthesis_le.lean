-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_norm_defect_synthesis_le
-- name    : BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:54:03.770787+00:00
-- url     : https://prove2.me/theorems/bb4e2a2c-b697-4997-a9e8-41182e81e344
-- title:
--   {m d : ℕ} (w : Fin m → E) (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) {delta : ℝ} (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta) (c : EuclideanSpace ℂ...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le {m d : ℕ} (w : Fin m → E)
    (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) {delta : ℝ}
    (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta)
    (c : EuclideanSpace ℂ (Fin m)) :
    ‖synthesis w c - V (ContinuousLinearMap.adjoint V (synthesis w c))‖
      ≤ delta * (Real.sqrt m * ‖c‖) := by sorry
