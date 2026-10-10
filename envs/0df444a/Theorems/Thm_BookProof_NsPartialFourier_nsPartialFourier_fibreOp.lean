-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_fibreOp
-- name    : BookProof.NsPartialFourier.nsPartialFourier_fibreOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:10:49.78898+00:00
-- url     : https://prove2.me/theorems/9ed9986e-9bca-44c0-a09d-65d11769b56c
-- title:
--   `BookProof.NsPartialFourier.nsPartialFourier_fibreOp` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.nsPartialFourier_fibreOp` (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) : nsPartialFourier V W (fibreOp V T f) = fibreOp V T (nsPartialFourier V W f)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.nsPartialFourier_fibreOp`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.nsPartialFourier_fibreOp
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

theorem BookProof.NsPartialFourier.nsPartialFourier_fibreOp (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    nsPartialFourier V W (fibreOp V T f) = fibreOp V T (nsPartialFourier V W f) := by sorry
