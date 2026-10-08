-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_mixedOp_apply
-- name    : BookProof.FourierMultiplierEsa.fourier_mixedOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:02.725744+00:00
-- url     : https://prove2.me/theorems/91598c27-e60b-4781-a4ee-4d461e49c47d
-- title:
--   `BookProof.FourierMultiplierEsa.fourier_mixedOp_apply` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (mixedOp a c w κ f) : 𝓢(V, ℂ)) x = ((mixedSymbolFn a c...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.fourier_mixedOp_apply` (a c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (mixedOp a c w κ f) : 𝓢(V, ℂ)) x = ((mixedSymbolFn a c w κ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.fourier_mixedOp_apply`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.fourier_mixedOp_apply
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.fourier_mixedOp_apply (a c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (mixedOp a c w κ f) : 𝓢(V, ℂ)) x
      = ((mixedSymbolFn a c w κ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
