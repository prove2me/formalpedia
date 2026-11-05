-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:01:15.002013+00:00
-- url     : https://prove2.me/theorems/5ed227ef-9d17-41f0-b96c-09814158b0cf
-- title:
--   Vanishing far-left tail of a finite real Borel measure
-- statement:
--   The mass of (-∞,-n] under an arbitrary finite positive Borel measure on the real line tends to zero as n tends to infinity. This is a quantitative-tightness component for the zero endpoint of logarithmic inversion of exponential mark images.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero (μ : Measure ℝ) [IsFiniteMeasure μ] : Tendsto (fun n : ℕ => μ (Iic (-(n : ℝ)))) atTop (𝓝 0) := by sorry
