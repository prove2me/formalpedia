-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_partialFourier_norm
-- name    : BookProof.NsPartialFourier.partialFourier_norm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:56:53.586283+00:00
-- url     : https://prove2.me/theorems/2c36ff63-4eac-4e30-913c-e29fe617abc9
-- title:
--   `BookProof.NsPartialFourier.partialFourier_norm` (v : Lp F 2 (volume : Measure V)) : ‖partialFourier V F v‖ = ‖v‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.partialFourier_norm` (v : Lp F 2 (volume : Measure V)) : ‖partialFourier V F v‖ = ‖v‖
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.partialFourier_norm`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.partialFourier_norm
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

theorem BookProof.NsPartialFourier.partialFourier_norm (v : Lp F 2 (volume : Measure V)) :
    ‖partialFourier V F v‖ = ‖v‖ := by sorry
