-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:24:23.080749+00:00
-- url     : https://prove2.me/theorems/389a618c-8fb0-4164-afac-c2bfd197c65d
-- title:
--   Instant ruin original capped complete Stieltjes dividend reward bounded by initial capital
-- statement:
--   On any path of a capped admissible dividend strategy for which the original spectrally negative Levy reserve ruins instantaneously, the entire original discounted dividend Stieltjes reward through every nonnegative closed horizon is its time-zero atom, which is no larger than the initial reserve x. The result holds pathwise for all discount rates and does not assume bounded variation.
-- source:
--   Original ruin=0 payment-time convention, canonical time-zero Stieltjes atom identity, and actual capped-admissible post-initial-payment reserve nonnegativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ≥0) (ω : Ω)
    (hruin : ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal x := by sorry
