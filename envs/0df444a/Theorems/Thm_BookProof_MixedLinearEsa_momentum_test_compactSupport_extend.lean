-- Prove2me | Theorems.Thm_BookProof_MixedLinearEsa_momentum_test_compactSupport_extend
-- name    : BookProof.MixedLinearEsa.momentum_test_compactSupport_extend
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:05:07.100274+00:00
-- url     : https://prove2.me/theorems/32731e23-4011-49d4-9e48-efb4078c4d70
-- title:
--   `BookProof.MixedLinearEsa.momentum_test_compactSupport_extend` (m : V) (z : ℂ) (w : Lp ℂ 2 (volume : Measure V)) (hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) → ∫ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedLinearEsa`.
--
--   `BookProof.MixedLinearEsa.momentum_test_compactSupport_extend` (m : V) (z : ℂ) (w : Lp ℂ 2 (volume : Measure V)) (hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) → ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x) = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x)) (f : 𝓢(V, ℂ)) : ∫ x, (starRingEnd ℂ) ((momentumOp m f) x) * (w x) = z * ∫ x, (starRingEnd ℂ) (f x) * (w x)
--
--   Formalization note: Lean 4 identifier `BookProof.MixedLinearEsa.momentum_test_compactSupport_extend`.

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.momentum_test_compactSupport_extend
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

theorem BookProof.MixedLinearEsa.momentum_test_compactSupport_extend (m : V) (z : ℂ) (w : Lp ℂ 2 (volume : Measure V))
    (hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x))
    (f : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) ((momentumOp m f) x) * (w x)
      = z * ∫ x, (starRingEnd ℂ) (f x) * (w x) := by sorry
