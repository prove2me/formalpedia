-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:41:50.409479+00:00
-- url     : https://prove2.me/theorems/392d2bb3-b29d-4e14-8b04-f1dbe3f3aa57
-- title:
--   Original BV complete discounted Stieltjes expected cash bound under any bounded random clock
-- statement:
--   For the actual standing bounded-variation spectrally negative Lévy source and genuinely capped admissible dividend strategy, the complete discounted Stieltjes payout through any path-dependent nonnegative clock bounded pointwise by a deterministic T has an expected ENNReal bound by initial capital plus physical drift over T+1. No stopping-time measurability assumption is necessary for this upper-integral monotonicity. The time-zero atom, all continuous and singular-continuous payouts, the payment at the random terminal point, and right-continuous ruin stopping remain in their original source objects. This follows from the previously proved unconditional complete closed-horizon BV drift budget, not from the desired HJB inequality.
-- source:
--   Original Avram Dividend Classical bounded-variation payout localisation; accepted source budget UUID 610138f4-4687-442b-8924-d213af477085, deterministic closed horizon to bounded random upper clock by monotone ENNReal Stieltjes integrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal
        (x + (((T + 1 : ℝ≥0) : ℝ) * X.drift)) := by sorry
