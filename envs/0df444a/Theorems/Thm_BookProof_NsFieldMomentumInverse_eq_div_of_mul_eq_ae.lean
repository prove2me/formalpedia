-- Prove2me | Theorems.Thm_BookProof_NsFieldMomentumInverse_eq_div_of_mul_eq_ae
-- name    : BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:22.377129+00:00
-- url     : https://prove2.me/theorems/354a5da7-32ff-4c85-b707-fa6b3628a1d5
-- title:
--   `BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae` {m : W} (hm : m ≠ 0) (t : W → ℂ) (p : ℂ) (h : ∀ᵐ ξ ∂(volume : Measure W), ((momSymbol m ξ : ℝ) : ℂ) * t ξ = p) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsFieldMomentumInverse`.
--
--   `BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae` {m : W} (hm : m ≠ 0) (t : W → ℂ) (p : ℂ) (h : ∀ᵐ ξ ∂(volume : Measure W), ((momSymbol m ξ : ℝ) : ℂ) * t ξ = p) : ∀ᵐ ξ ∂(volume : Measure W), t ξ = p / ((momSymbol m ξ : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae`.

-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
open BookProof.NsFieldMomentumInverse



open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae {m : W} (hm : m ≠ 0) (t : W → ℂ) (p : ℂ)
    (h : ∀ᵐ ξ ∂(volume : Measure W), ((momSymbol m ξ : ℝ) : ℂ) * t ξ = p) :
    ∀ᵐ ξ ∂(volume : Measure W), t ξ = p / ((momSymbol m ξ : ℝ) : ℂ) := by sorry
