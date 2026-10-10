-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_apply
-- name    : BookProof.MixedLinearEsa.momentumOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:04:32.832932+00:00
-- url     : https://prove2.me/theorems/36219611-b286-493b-a426-c3a9e976a293
-- title:
--   `BookProof.MixedLinearEsa.momentumOp_apply` (m : V) (f : 𝓢(V, ℂ)) (x : V) : (momentumOp m f) x = (-Complex.I) * (fderiv ℝ f x m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.momentumOp_apply` (m : V) (f : 𝓢(V, ℂ)) (x : V) : (momentumOp m f) x = (-Complex.I) * (fderiv ℝ f x m)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.momentumOp_apply`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.momentumOp_apply
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

theorem BookProof.MixedLinearEsa.momentumOp_apply (m : V) (f : 𝓢(V, ℂ)) (x : V) :
    (momentumOp m f) x = (-Complex.I) * (fderiv ℝ f x m) := by sorry
