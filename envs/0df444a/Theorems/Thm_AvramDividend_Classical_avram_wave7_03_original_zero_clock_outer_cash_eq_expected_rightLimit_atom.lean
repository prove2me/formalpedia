-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_zero_clock_outer_cash_eq_expected_rightLimit_atom
-- name    : AvramDividend.Classical.avram_wave7_03_original_zero_clock_outer_cash_eq_expected_rightLimit_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:45:59.669452+00:00
-- url     : https://prove2.me/theorems/1fda88bd-a7d5-4167-bbc0-ece35b31dd95
-- title:
--   Original double ENNReal ruin-stopped zero-clock payout equals expected right-limit time-zero Stieltjes atom
-- statement:
--   For every original spectrally negative Lévy process X, source P, source dividend strategy D and arbitrary real q, the exact double expected discounted dividendMeasure Stieltjes lintegral over canonical paymentTimes(ruinTime X x D ω)∩Iic0 equals the ENNReal expectation under original P of ENNReal.ofReal(rightLimit D 0 ω). This is an explicit outer-measure zero-clock right-payment bridge, without density assumptions, discount monotonicity or surrogate processes. The time-zero atom is retained even when ruinTime=0; its identity follows from exact proved zero-clock reward and original Stieltjes closed-interval mass formula.
-- source:
--   Proved original zero-clock full Stieltjes atom theorem 1fb597ac-8e48-41be-a4e3-03b7681f3915 and original dividendMeasure Icc rightLimit theorem d6ace15b-26cc-4400-be9b-8c4d19980128.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_zero_clock_outer_cash_eq_expected_rightLimit_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P := by sorry
