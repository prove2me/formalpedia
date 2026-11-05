-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:04:08.217125+00:00
-- url     : https://prove2.me/theorems/e5d4e456-e7fa-4fc8-b1a9-c931ac2514a0
-- title:
--   Vanishing zero-endpoint tail of finite exponential mark images
-- statement:
--   For any finite positive Borel real measure σ, its exponential image assigns vanishing mass to (−∞,exp(−n)] as n tends to infinity. This is the finite-measure endpoint control required to transport compact continuous tests via log, using only a source-independent cutoff equality and continuity from above.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail (σ : Measure ℝ) [IsFiniteMeasure σ] : Tendsto (fun n : ℕ => (σ.map Real.exp) (Iic (Real.exp (-(n : ℝ))))) atTop (𝓝 0) := by sorry
