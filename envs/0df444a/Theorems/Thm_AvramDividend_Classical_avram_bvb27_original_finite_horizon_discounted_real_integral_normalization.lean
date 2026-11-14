-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_finite_horizon_discounted_real_integral_normalization
-- name    : AvramDividend.Classical.avram_bvb27_original_finite_horizon_discounted_real_integral_normalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:13:11.593985+00:00
-- url     : https://prove2.me/theorems/3ab4e2bc-4b01-4e4f-b175-fa4e12ecf80b
-- title:
--   Original finite physical horizon real exponential discount budget identity from FTC, without positive-q divisions
-- statement:
--   For any real discount q and finite physical observation horizon T, the real integral of the original source exponential discount exp(-qt) over the exact interval from physical time zero to T, multiplied by q, plus the terminal exponential discount exp(-qT), equals one. This exact deterministic FTC identity is the real-valued core of the ENNReal discount clock normalisation premise in the already accepted zero-contact cash-terminal HJB inequality 09a9c1c4. It requires neither a modified time clock nor a probabilistic measure.
-- source:
--   Pinned Mathlib intervalIntegral.integral_eq_sub_of_hasDerivAt and Real.hasDerivAt_exp, original source discount q in ed067740 and 09a9c1c4.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb27_original_finite_horizon_discounted_real_integral_normalization
    (q T : ℝ) :
    q * (∫ t in (0 : ℝ)..T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) +
      Real.exp (-(q * T)) = 1 := by sorry
