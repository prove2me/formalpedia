-- Prove2me | Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_firstOrderOp_apply
-- name    : BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:23:03.417988+00:00
-- url     : https://prove2.me/theorems/f7f8c5a3-cb6b-41f0-a543-c4dbab479bcd
-- title:
--   `BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply` (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (firstOrderOp c w f) : 𝓢(V, ℂ)) x = ((foSymbolFn c w x : ℝ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFourierMultiplierEsa`.
--
--   `BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply` (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (firstOrderOp c w f) : 𝓢(V, ℂ)) x = ((foSymbolFn c w x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply`.

-- Generated from ChapterFourierMultiplierEsa.lean — theorem BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (firstOrderOp c w f) : 𝓢(V, ℂ)) x
      = ((foSymbolFn c w x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
