-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_partialFourier_inner
-- name    : BookProof.NsPartialFourier.partialFourier_inner
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:56:33.304046+00:00
-- url     : https://prove2.me/theorems/b13d4127-4061-4ad8-ac17-4e90e7ca44f1
-- title:
--   `BookProof.NsPartialFourier.partialFourier_inner` (v u : Lp F 2 (volume : Measure V)) : (inner ℂ (partialFourier V F v) (partialFourier V F u) : ℂ) = inner ℂ v u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.partialFourier_inner` (v u : Lp F 2 (volume : Measure V)) : (inner ℂ (partialFourier V F v) (partialFourier V F u) : ℂ) = inner ℂ v u
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.partialFourier_inner`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.partialFourier_inner
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable (V F) in

theorem BookProof.NsPartialFourier.partialFourier_inner (v u : Lp F 2 (volume : Measure V)) :
    (inner ℂ (partialFourier V F v) (partialFourier V F u) : ℂ) = inner ℂ v u := by sorry
