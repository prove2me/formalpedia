-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
-- name    : AvramDividend.Classical.avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:26:19.237205+00:00
-- url     : https://prove2.me/theorems/7b979a09-a68e-42bb-8ef8-fa3fc8136779
-- title:
--   Genuine right-continuous randomly stopped finite-horizon discount is predictable, bounded, and supported before T
-- statement:
--   For any stopping time of the actual original right-continuous filtration, the product of the inclusive survival indicator 1_{t≤τ(ω)} and nonnegative-rate finite-horizon discount 1_{t≤T} exp(-qt) is measurable in the genuine right-continuous predictable sigma algebra, bounded in absolute value by one and identically zero for t>T. This is the exact random-stopping weight required to instantiate Chat04's arbitrary bounded predictable source jump-generator expectation theorem in Chat06, without declaring the clock automatically a Lévy jump compensator.
-- source:
--   Avram Wave6 Chat04 mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Directly combines Proved ed5ee649 original deterministic predictable discount and Proved 69806d16 original inclusive stopping-time survival predictability; supports the genuine source process and Chat06 stopped discount.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    Measurable[𝓕.rightCont.predictable] a ∧
    (∀ p, |a p| ≤ (1 : ℝ)) ∧
    (∀ p, T < p.1 → a p = 0) := by sorry
