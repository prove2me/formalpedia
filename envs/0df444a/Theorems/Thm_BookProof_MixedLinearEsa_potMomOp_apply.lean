-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_apply
-- name    : BookProof.MixedLinearEsa.potMomOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:06:58.708678+00:00
-- url     : https://prove2.me/theorems/66ba6efa-bb43-4d28-b314-bfff252d5211
-- title:
--   `BookProof.MixedLinearEsa.potMomOp_apply` {W : V → ℝ} (hW : Function.HasTemperateGrowth W) (m : V) (f : 𝓢(V, ℂ)) (x : V) : (potMomOp W m f) x = ((W x : ℝ) : ℂ) * f x + (-Complex.I)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.potMomOp_apply` {W : V → ℝ} (hW : Function.HasTemperateGrowth W) (m : V) (f : 𝓢(V, ℂ)) (x : V) : (potMomOp W m f) x = ((W x : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.potMomOp_apply`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.potMomOp_apply
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterWaveUnboundedPotential
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.MixedLinearEsa.potMomOp_apply {W : V → ℝ} (hW : Function.HasTemperateGrowth W) (m : V) (f : 𝓢(V, ℂ))
    (x : V) :
    (potMomOp W m f) x = ((W x : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m) := by sorry
