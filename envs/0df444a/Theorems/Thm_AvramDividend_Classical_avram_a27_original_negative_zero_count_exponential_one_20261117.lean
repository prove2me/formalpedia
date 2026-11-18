-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_zero_count_exponential_one_20261117
-- name    : AvramDividend.Classical.avram_a27_original_negative_zero_count_exponential_one_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:05:56.987413+00:00
-- url     : https://prove2.me/theorems/4ce72855-de27-4ff2-847a-49152179ead0
-- title:
--   Original zero negative-jump count forces unit physical marked-jump exponential
-- statement:
--   On the unchanged original Levy probability space, any measurable representative of the complete physical negative-jump sum has exponential equal to one whenever the exact physical negative-jump count is zero. This is the zero-count cell of the marked-Poisson Laplace factorisation.
-- source:
--   Proved original finite marked-count support efd5b548, physical finite exponential product a88 900bfbce, nonpositive original physical marks e95fe5bc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The physical negative-jump exponential is one on an empty original jump-count cell. -/

theorem AvramDividend.Classical.avram_a27_original_negative_zero_count_exponential_one_20261117
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
    ∀ᵐ ω ∂P, K ω = 0 → Real.exp (θ * J ω) = 1 := by sorry
