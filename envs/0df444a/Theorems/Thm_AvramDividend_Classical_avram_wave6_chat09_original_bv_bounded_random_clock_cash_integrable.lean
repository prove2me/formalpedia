-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:55:53.379822+00:00
-- url     : https://prove2.me/theorems/5817eddd-8064-458e-9897-cff0b92a2b65
-- title:
--   Original BV bounded random-clock complete real Stieltjes cash is L¹ integrable
-- statement:
--   Under the actual standing bounded-variation spectrally negative Lévy source and genuinely cap-admissible original left-continuous dividends, any measurable real-valued random clock bounded by a deterministic finite nonnegative T has integrable real discounted complete stopped Stieltjes payout. The result combines the Proved original-source random inclusive clock Stieltjes cash measurability and the Proved BV random-clock drift expectation bound. It retains payments at zero, singular-continuous dividends and the terminal right-limit atom. No HJB inequality, martingale budget or result-equivalent bound is assumed.
-- source:
--   Original source random inclusive cash measurability UUID 2d478c7d and original BV bounded random-clock drift expectation UUID 392d2bb3, via Mathlib MeasureTheory.integrable_toReal_of_lintegral_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => ((τ ω : ℝ≥0) : ℝ))) :
    Integrable
      (fun ω => (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
