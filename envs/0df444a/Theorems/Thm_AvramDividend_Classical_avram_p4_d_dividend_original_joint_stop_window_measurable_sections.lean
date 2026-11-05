-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_joint_stop_window_measurable_sections
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_joint_stop_window_measurable_sections
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:06:58.953206+00:00
-- url     : https://prove2.me/theorems/a56e29e5-8731-4583-9a43-93e93764c89f
-- title:
--   Original right-dividend pre-ruin closed-horizon payment window has measurable pathwise sections
-- statement:
--   For the actual source paymentTimes at the ruin stopping clock intersected with the closed horizon Iic T, measurability of the joint stopped-payment window implies Borel measurability at every fixed sample path. This removes the separate pathwise-measurable-window hypothesis in the P4-D s-finite dividend-integral measurability bridge when the joint stopping window is available.
-- source:
--   Original IsDividendStrategy definitions of paymentTimes, with pinned Mathlib Measurable.prodMk and MeasurableSet.preimage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_joint_stop_window_measurable_sections
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (hJoint : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    ∀ ω : Ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)) := by sorry
