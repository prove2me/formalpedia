-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_one_negative_jump_exponential_unique_mark_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_one_negative_jump_exponential_unique_mark_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:43:33.311634+00:00
-- url     : https://prove2.me/theorems/c932c121-d840-40cf-8ad1-4bb5d5c86870
-- title:
--   Original physical negative jump exponential on a single-count cell equals the actual unique jump factor
-- statement:
--   When the original actual physical negative-jump count equals one, the full physical negative-jump Laplace exponential equals the exponential of that unique negative jump. This isolates the one-jump conditional mark law on the unchanged original probability space.
-- source:
--   Proved original physical finite marked-support/cardinality, original finite exponential product, and original nonpositive physical jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One actual negative physical jump makes the exponential weight its unique marked factor. -/

theorem AvramDividend.Classical.avram_a27_original_physical_one_negative_jump_exponential_unique_mark_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    ∀ᵐ ω ∂P, K ω = 1 →
      ∃ u : ℝ≥0, 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        Real.exp (θ * J ω) =
          Real.exp (θ * (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
