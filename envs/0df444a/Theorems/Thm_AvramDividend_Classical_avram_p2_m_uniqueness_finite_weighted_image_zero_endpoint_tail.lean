-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_weighted_image_zero_endpoint_tail
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_finite_weighted_image_zero_endpoint_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:20:39.082108+00:00
-- url     : https://prove2.me/theorems/e7d9fdb4-f04b-421a-bdf8-180ee373a436
-- title:
--   Zero-endpoint tail for finite weighted exponential images of arbitrary source rates
-- statement:
--   Even if the original real mark-rate σ is infinite, whenever the weighted exponential image (σ.withDensity w).map exp is finite, its mass on (−∞,exp(−n)] tends to zero. The proof recovers finiteness of the weighted source by exact map mass preservation and invokes the finite endpoint theorem, avoiding any global finite-rate assumption.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_finite_weighted_image_zero_endpoint_tail (σ : Measure ℝ) (w : ℝ → ℝ≥0∞) [IsFiniteMeasure ((σ.withDensity w).map Real.exp)] : Tendsto (fun n : ℕ => ((σ.withDensity w).map Real.exp) (Iic (Real.exp (-(n : ℝ))))) atTop (𝓝 0) := by sorry
