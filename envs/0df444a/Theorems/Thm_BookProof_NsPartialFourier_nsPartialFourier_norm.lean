-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_norm
-- name    : BookProof.NsPartialFourier.nsPartialFourier_norm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:56.609973+00:00
-- url     : https://prove2.me/theorems/67d7c8c6-ea8e-435a-ae04-d6292510b839
-- title:
--   `BookProof.NsPartialFourier.nsPartialFourier_norm` (v : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) : ‖nsPartialFourier V W v‖ = ‖v‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.nsPartialFourier_norm` (v : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) : ‖nsPartialFourier V W v‖ = ‖v‖
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.nsPartialFourier_norm`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.nsPartialFourier_norm
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
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem BookProof.NsPartialFourier.nsPartialFourier_norm (v : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    ‖nsPartialFourier V W v‖ = ‖v‖ := by sorry
