-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
-- name    : AvramDividend.Classical.avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:53:53.481028+00:00
-- url     : https://prove2.me/theorems/191f919b-68cd-491e-98e7-375f6382ab18
-- title:
--   First and second falling-factorial moments squeeze probability of a positive integer count
-- statement:
--   For any measurable natural-valued random count on a probability space, if its first real and second falling-factorial real functions are integrable, E[K] - E[K(K−1)]/2 ≤ P(K≠0) ≤ E[K]. Prove by integrating the deterministic integer-count occupancy sandwich, using the indicator integral = probability and linearity of Bochner integration. This source-independent result bridges Proved original physical negative-Borel first and second factorial moments to the small-time Poisson void deficit bound.
-- source:
--   Mathlib integral_mono_ae, integral_sub, integral_div_const, integral_indicator_one and physical count integer occupancy bound.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hSecond : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (∫ ω, (K ω : ℝ) ∂P) -
        (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 ≤
      (P {ω : Ω | K ω ≠ 0}).toReal ∧
    (P {ω : Ω | K ω ≠ 0}).toReal ≤
      (∫ ω, (K ω : ℝ) ∂P) := by sorry
