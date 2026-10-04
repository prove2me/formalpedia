-- Prove2me | Theorems.Thm_AvramDividend_Classical_additive_convolution_total_mass
-- name    : AvramDividend.Classical.additive_convolution_total_mass
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T23:53:08.255822+00:00
-- url     : https://prove2.me/theorems/7b928beb-3819-45df-9e0b-ee6a6d3b7e6a
-- title:
--   Total mass multiplies under convolution of finite or s-finite real measures
-- statement:
--   For any two measures on the real additive group, the total mass of their additive convolution equals the product of their total masses, including the extended-real cases. This is the exact algebraic foundation needed to prove that if the exponentially discounted BV renewal kernel has mass r<1 then its n-fold convolution has mass r^n, so the entire renewal resolvent is a finite geometric series before discounting is reversed.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_conv_eq_lintegral_prod, Measure.prod_prod, Set.univ_prod_univ

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Total mass of additive convolution of two real measures
is the product of their total masses, in ℝ≥0∞. -/
theorem additive_convolution_total_mass (μ ν : Measure ℝ) :
    (Measure.conv μ ν) Set.univ = μ Set.univ * ν Set.univ := by
  sorry

end AvramDividend.Classical
