-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_fibreFourier
-- name    : BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:11:32.09359+00:00
-- url     : https://prove2.me/theorems/d01c1e58-58b4-4703-8bf3-4eedb484392f
-- title:
--   `BookProof.NsPartialFourier.nsPartialFourier_fibreFourier` (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) : nsPartialFourier V W (fibreOp V (fibreFourierCLM W) f) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.nsPartialFourier_fibreFourier` (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) : nsPartialFourier V W (fibreOp V (fibreFourierCLM W) f) = fibreOp V (fibreFourierCLM W) (nsPartialFourier V W f)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.nsPartialFourier_fibreFourier`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
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

theorem BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
    (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    nsPartialFourier V W (fibreOp V (fibreFourierCLM W) f)
      = fibreOp V (fibreFourierCLM W) (nsPartialFourier V W f) := by sorry
