-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
-- name    : AvramDividend.Classical.avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:51:17.317819+00:00
-- url     : https://prove2.me/theorems/ec132215-405e-497b-a774-db3af53df6e4
-- title:
--   Actual original strictly pre-ruin random-clock payment region is exactly the complete closed time interval
-- statement:
--   At any path ω and any random finite nonnegative clock τ strictly before the genuine original ruinTime X x D ω, the exact source paymentTimes (ruinTime) intersected with the inclusive clock is [0,τ]. This deterministic same-source set equality retains the time-zero dividend atom and all positive-time Stieltjes payments, and is the missing alignment needed to use a closed [0,τ] clipped-grid Stieltjes estimate for the actual original ruin-stopped cash observable. No stochastic Ito formula or unproved compensator is assumed.
-- source:
--   Avram Proposition 4(i), genuine paymentTimes strict ruin convention; accepted canonical paymentTimes_eq_strict_of_pos 7c01995b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      Icc (0 : ℝ) (τ ω : ℝ) := by sorry
