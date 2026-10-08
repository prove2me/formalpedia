-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_momentumOp_apply
-- name    : BookProof.FourierMultiplierEsa.fourier_momentumOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:34.638561+00:00
-- url     : https://prove2.me/theorems/bf3b3648-54f4-4c17-bc59-95c7f439d77e
-- title:
--   `BookProof.FourierMultiplierEsa.fourier_momentumOp_apply` (f : 𝓢(V, ℂ)) (m : V) (x : V) : (𝓕 (momentumOp m f) : 𝓢(V, ℂ)) x = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) * (𝓕 f...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.fourier_momentumOp_apply` (f : 𝓢(V, ℂ)) (m : V) (x : V) : (𝓕 (momentumOp m f) : 𝓢(V, ℂ)) x = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.fourier_momentumOp_apply`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.fourier_momentumOp_apply
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.fourier_momentumOp_apply (f : 𝓢(V, ℂ)) (m : V) (x : V) :
    (𝓕 (momentumOp m f) : 𝓢(V, ℂ)) x
      = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
