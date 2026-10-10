-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_apply
-- name    : BookProof.MixedLinearEsa.mixedLinearOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:04:04.311428+00:00
-- url     : https://prove2.me/theorems/a47dcb04-6f3d-4d41-8f5c-d1119c4d0efd
-- title:
--   `BookProof.MixedLinearEsa.mixedLinearOp_apply` (b m : V) (f : 𝓢(V, ℂ)) (x : V) : (mixedLinearOp b m f) x = ((inner ℝ x b : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.mixedLinearOp_apply` (b m : V) (f : 𝓢(V, ℂ)) (x : V) : (mixedLinearOp b m f) x = ((inner ℝ x b : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.mixedLinearOp_apply`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_apply
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

theorem BookProof.MixedLinearEsa.mixedLinearOp_apply (b m : V) (f : 𝓢(V, ℂ)) (x : V) :
    (mixedLinearOp b m f) x
      = ((inner ℝ x b : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m) := by sorry
