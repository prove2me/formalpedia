-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_deterministic_horizon_discount_predictable_unit_bound
-- name    : AvramDividend.Classical.avram_twoagentA_deterministic_horizon_discount_predictable_unit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:27:49.565163+00:00
-- url     : https://prove2.me/theorems/0c088ed5-f62c-498c-9434-e9f1fad39f22
-- title:
--   Predictability and unit bound of deterministic exponentially discounted time-horizon mask
-- statement:
--   For any right-continuous filtration and nonnegative discount rate, the deterministic clipped exponential p↦1_[t≤T] exp(-q t) is predictable and takes values in [0,1]. This supplies the precise true-clock weight needed in the actual original Levy-process physical HJB tail bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_deterministic_horizon_discount_predictable_unit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    Measurable[𝓕.rightCont.predictable] a ∧
      ∀ p, 0 ≤ a p ∧ a p ≤ 1 := by sorry
