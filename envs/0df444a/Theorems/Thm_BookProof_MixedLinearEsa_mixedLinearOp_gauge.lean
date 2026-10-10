-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_gauge
-- name    : BookProof.MixedLinearEsa.mixedLinearOp_gauge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:07:09.956983+00:00
-- url     : https://prove2.me/theorems/396cf087-c8be-4b90-87a3-4235d8303a5a
-- title:
--   `BookProof.MixedLinearEsa.mixedLinearOp_gauge` (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) : (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.mixedLinearOp_gauge` (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) : (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x = gaugeFun b m x * (momentumOp m φ x)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.mixedLinearOp_gauge`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_gauge
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.MixedLinearEsa.mixedLinearOp_gauge (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x
      = gaugeFun b m x * (momentumOp m φ x) := by sorry
