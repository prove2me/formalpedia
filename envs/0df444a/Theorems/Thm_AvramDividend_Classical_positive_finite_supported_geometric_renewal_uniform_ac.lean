-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform_ac
-- name    : AvramDividend.Classical.positive_finite_supported_geometric_renewal_uniform_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:48:31.385993+00:00
-- url     : https://prove2.me/theorems/2a0ef0b9-adb6-4eea-b919-d1a070088306
-- title:
--   Finite geometric renewal measure with positive-axis Lebesgue density and uniform Laplace identity
-- statement:
--   Under a subcritical finite positive jump-tail measure κ supported on [0,∞) and absolutely continuous with respect to Lebesgue volume, construct the geometric renewal measure β with positive finite total mass, nonnegative support, absolute continuity off the initial atom, finite cumulative mass at every x, and the exact all-s>0 positive Laplace identity of the Esscher shifted scale function. This is the strengthened explicit renewal witness needed in corrected bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9), then the continuous BV renewal density, scale-function C1, finite cstar, and the mission root.
-- source:
--   Accepted positive_finite_supported_geometric_renewal_uniform proof, factored nonnegative support convolution lemma, geometric_convolution_renewal_positive_part_ac.

import Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_finite_supported_geometric_renewal_uniform_ac
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκac : κ ≪ (volume : Measure ℝ))
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          (δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by sorry
