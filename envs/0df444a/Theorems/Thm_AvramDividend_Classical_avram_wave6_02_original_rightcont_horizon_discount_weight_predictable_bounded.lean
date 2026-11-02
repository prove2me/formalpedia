-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
-- name    : AvramDividend.Classical.avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:40:32.702691+00:00
-- url     : https://prove2.me/theorems/ed5ee649-2acf-41d1-b048-eb113d9a3a5d
-- title:
--   Original right-continuous predictable finite-horizon discount weight is measurable and bounded by one
-- statement:
--   For any original filtration on the actual sample space, its right-continuous predictable sigma algebra contains the deterministic nonnegative discounted time weight exp(-qt) stopped at finite horizon T. This weight is jointly predictable, has absolute value at most 1 for q>=0, and vanishes strictly after T, enabling source-specific compensated Taylor jump cancellation.
-- source:
--   Canonical Mathlib Probability.Process.Predictable predictable Ioi product generators and measurable_of_Ioi; continuous exponential and q>=0 bound; necessary deterministic input to the original source-specific controlled stopped compensated jump theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    Measurable[𝓕.rightCont.predictable] a ∧
    (∀ p, |a p| ≤ (1 : ℝ)) ∧
    (∀ p, T < p.1 → a p = 0) := by sorry
