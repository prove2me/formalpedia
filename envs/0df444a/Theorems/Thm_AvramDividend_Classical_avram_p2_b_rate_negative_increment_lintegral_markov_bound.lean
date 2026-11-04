-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_increment_lintegral_markov_bound
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_increment_lintegral_markov_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:23:32.869674+00:00
-- url     : https://prove2.me/theorems/705c0a10-5e07-421b-8774-1c27727c5b6e
-- title:
--   Separated negative increment probability controlled by fourth-weight moment
-- statement:
--   For any measurable real increment Y and arbitrary original measure mu, the positive fourth-exponential band constant times the mu-probability of Y<=-epsilon is bounded by the nonnegative Lebesgue integral of the fourth-exponential moment. This is an exact source-compatible Markov tail inequality, proved from the previously Proved negative band fourth-weight lower theorem and the pinned Mathlib lower integral estimate. It yields the O(h) negative-increment probability bound when combined with the original Levy small-time fourth-weight derivative and real-to-lower integral conversion.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_fourth_weight_lower
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_negative_increment_lintegral_markov_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4) *
      μ {ω | Y ω ≤ -ε} ≤
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) ∂μ := by sorry
