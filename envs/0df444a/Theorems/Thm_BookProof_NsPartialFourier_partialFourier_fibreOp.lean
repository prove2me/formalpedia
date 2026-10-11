-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_partialFourier_fibreOp
-- name    : BookProof.NsPartialFourier.partialFourier_fibreOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:47.370982+00:00
-- url     : https://prove2.me/theorems/3bd21bd3-940d-4def-9bbe-3db6afbb45f4
-- title:
--   `BookProof.NsPartialFourier.partialFourier_fibreOp` (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) : partialFourier V G (fibreOp V T f) = fibreOp V T (partialFourier V F f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.partialFourier_fibreOp` (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) : partialFourier V G (fibreOp V T f) = fibreOp V T (partialFourier V F f)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.partialFourier_fibreOp`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.partialFourier_fibreOp
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

theorem BookProof.NsPartialFourier.partialFourier_fibreOp (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) :
    partialFourier V G (fibreOp V T f) = fibreOp V T (partialFourier V F f) := by sorry
