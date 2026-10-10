-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_comp_fibreFourier_eq
-- name    : BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:11:21.730948+00:00
-- url     : https://prove2.me/theorems/0c4ed20b-8cf8-42d6-8534-9b10c5a92f90
-- title:
--   `BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq` : ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap).comp (fibreOp V (fibreFourierCLM W)) = (fibreOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq` : ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap).comp (fibreOp V (fibreFourierCLM W)) = (fibreOp V (fibreFourierCLM W)).comp ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap)
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
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

theorem BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq :
    ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap).comp
        (fibreOp V (fibreFourierCLM W))
      = (fibreOp V (fibreFourierCLM W)).comp
        ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap) := by sorry
