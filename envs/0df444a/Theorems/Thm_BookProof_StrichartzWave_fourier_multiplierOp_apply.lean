-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_fourier_multiplierOp_apply
-- name    : BookProof.StrichartzWave.fourier_multiplierOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:20:31.672196+00:00
-- url     : https://prove2.me/theorems/ac9b46ea-b2a5-4f80-996a-a6343b6c4b1a
-- title:
--   `BookProof.StrichartzWave.fourier_multiplierOp_apply` {m : V → ℝ} (hm : Function.HasTemperateGrowth m) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) x = ((m x : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.fourier_multiplierOp_apply` {m : V → ℝ} (hm : Function.HasTemperateGrowth m) (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) x = ((m x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.fourier_multiplierOp_apply`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.fourier_multiplierOp_apply
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.fourier_multiplierOp_apply {m : V → ℝ} (hm : Function.HasTemperateGrowth m)
    (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) x = ((m x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
