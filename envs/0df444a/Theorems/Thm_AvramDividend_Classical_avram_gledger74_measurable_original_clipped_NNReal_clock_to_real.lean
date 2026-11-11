-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
-- name    : AvramDividend.Classical.avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:50:24.648131+00:00
-- url     : https://prove2.me/theorems/2ed693fb-b1ff-404c-be5e-b365b04be47e
-- title:
--   Original measurable finite stopping clock has measurable real clipped deterministic endpoints
-- statement:
--   The original nonnegative random stopping horizon, viewed as a measurable WithTop clock, yields measurable real-valued clips at every deterministic nonnegative endpoint. This is the exact real-time part of the physical source observation package gledger71.
-- source:
--   Root-connected gledger71 exact physical stopped-grid measurability; gledger67 supplies the original WithTop clock.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ρ : Ω → ℝ≥0)
    (hρ : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)))
    (a : ℝ≥0) :
    Measurable (fun ω => ((min a (ρ ω) : ℝ≥0) : ℝ)) := by sorry
