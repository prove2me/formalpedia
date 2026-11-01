-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_l2_conditional_centering_closed_under_band_limit
-- name    : AvramDividend.Classical.avram_wave4_p1_l2_conditional_centering_closed_under_band_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:20:45.778448+00:00
-- url     : https://prove2.me/theorems/675ebf1e-e87c-449c-a4f0-c2c72983329b
-- title:
--   Conditional martingale-difference centering survives the infinite-activity L² marked-band limit
-- statement:
--   For the original sample-space probability and an actual past sigma-algebra, show that a sequence of square-integrable finite-band compensated increments with zero conditional expectation converging in L² has a limiting increment with zero conditional expectation. This is closure of conditional centering under a verified L² limit, via continuous linear conditional expectation; no Poisson compensation or limit-martingale conclusion is assumed.
-- source:
--   Pinned Mathlib 0df444a MeasureTheory.Function.ConditionalExpectation.CondexpL2 condExpL2 continuous linear map, Topology.Separation.Hausdorff tendsto_nhds_unique.

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_l2_conditional_centering_closed_under_band_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast : MeasurableSpace Ω)
    (hPast : mPast ≤ mΩ)
    [@SigmaFinite Ω mPast (P.trim hPast)]
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (Mlimit : Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : Tendsto M Filter.atTop (nhds Mlimit))
    (hcenter : ∀ n, (MeasureTheory.condExpL2 ℝ ℝ hPast) (M n) = 0) :
    (MeasureTheory.condExpL2 ℝ ℝ hPast) Mlimit = 0 := by sorry
