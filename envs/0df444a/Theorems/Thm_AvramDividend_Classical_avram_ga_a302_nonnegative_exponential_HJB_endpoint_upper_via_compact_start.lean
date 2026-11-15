-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
-- name    : AvramDividend.Classical.avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:40:58.284867+00:00
-- url     : https://prove2.me/theorems/be7dbf2a-e626-49d0-8ee2-7cd1caeecb5f
-- title:
--   Upper HJB endpoint exponential at compact preincrement reserve reduces to original signed increment exponential envelope
-- statement:
--   If a positive Gaussian HJB supersolution has an upper envelope K exp(theta times post-increment reserve) and the original pre-increment reserve y is at most compact bound B, then the endpoint envelope is at most K exp(theta B) times exp(theta r) of the actual signed Gaussian increment r. This scalar inequality bridges the true stopped source a301 to proved signed original Gaussian expected-tail control a275 for a263.
-- source:
--   Original Gaussian source global HJB bound a257, compact stopped reserve envelope, signed rare Gaussian exponential tail a275.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
    (θ K B y r : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hy : y ≤ B) :
    K * Real.exp (θ * (y + r)) ≤
      (K * Real.exp (θ * B)) * Real.exp (θ * r) := by sorry
