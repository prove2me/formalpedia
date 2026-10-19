-- Prove2me | Theorems.Thm_BookProof_NsPartialFourier_fourier_vecMomentumOp_apply
-- name    : BookProof.NsPartialFourier.fourier_vecMomentumOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:19.565748+00:00
-- url     : https://prove2.me/theorems/087ebd82-6202-4f60-82c7-374de1e48e06
-- title:
--   `BookProof.NsPartialFourier.fourier_vecMomentumOp_apply` (m : V) (f : 𝓢(V, F)) (x : V) : (𝓕 (vecMomentumOp m f) : 𝓢(V, F)) x = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) • (𝓕 f...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsPartialFourier`.
--
--   `BookProof.NsPartialFourier.fourier_vecMomentumOp_apply` (m : V) (f : 𝓢(V, F)) (x : V) : (𝓕 (vecMomentumOp m f) : 𝓢(V, F)) x = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) • (𝓕 f : 𝓢(V, F)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NsPartialFourier.fourier_vecMomentumOp_apply`.

-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.fourier_vecMomentumOp_apply
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

theorem BookProof.NsPartialFourier.fourier_vecMomentumOp_apply (m : V) (f : 𝓢(V, F)) (x : V) :
    (𝓕 (vecMomentumOp m f) : 𝓢(V, F)) x
      = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) • (𝓕 f : 𝓢(V, F)) x := by sorry
