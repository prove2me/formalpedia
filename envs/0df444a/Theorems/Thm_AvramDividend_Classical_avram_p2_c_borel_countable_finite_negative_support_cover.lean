-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_countable_finite_negative_support_cover
-- name    : AvramDividend.Classical.avram_p2_c_borel_countable_finite_negative_support_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:31:41.510012+00:00
-- url     : https://prove2.me/theorems/7b0021fb-d137-47f8-9a53-0f61d30130ce
-- title:
--   Negative-supported locally finite-tail measure has countable measurable finite-mass exhaustion
-- statement:
--   Any real mark measure with zero nonnegative mass and finite mass on every negative halfline bounded away from zero admits a countable measurable cover by sets of finite measure: the nonnegative halfline plus harmonic separated negative bands. This is the exact sigma-finiteness construction needed for the source expected jump intensity.
-- source:
--   Explicit harmonic-cutoff exhaustion and Mathlib's tendsto_one_div_add_atTop_nhds_zero_nat, reusing the proven P2-C monotone exhaustion pattern; no ν rate or stochastic assumptions.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_countable_finite_negative_support_cover
    (μ : Measure ℝ)
    (hzero : μ (Ici (0 : ℝ)) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      (∀ n, μ (C n) < ⊤) ∧
      (⋃ n, C n) = univ := by sorry
