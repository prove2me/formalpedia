-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:39:54.76496+00:00
-- url     : https://prove2.me/theorems/bfe4a214-2dc7-40dc-b43d-19316d917a2e
-- title:
--   Original stopped payment region equals the closed clock interval at zero or strictly before ruin
-- statement:
--   For the true original source path and random finite clock τ, if τ=0 (including immediate ruin σ=0) or τ<σ, the original payable set paymentTimes σ intersected with times at most τ is exactly the complete closed interval [0,τ]. Its time-zero atom remains present even at immediate ruin; no assertion at strictly positive ruin time is made.
-- source:
--   Avram Proposition 4(i), original left-continuous dividend paymentTimes(ruinTime). Extends Proved ec132215 by direct zero-horizon case of source paymentTimes definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      Icc (0 : ℝ) (τ ω : ℝ) := by sorry
