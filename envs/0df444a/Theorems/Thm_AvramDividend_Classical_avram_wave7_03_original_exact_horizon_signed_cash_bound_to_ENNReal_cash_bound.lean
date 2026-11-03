-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_exact_horizon_signed_cash_bound_to_ENNReal_cash_bound
-- name    : AvramDividend.Classical.avram_wave7_03_original_exact_horizon_signed_cash_bound_to_ENNReal_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:02:21.414732+00:00
-- url     : https://prove2.me/theorems/24a93f7c-7592-44f5-9fba-b97188ecf51e
-- title:
--   Exact original bounded-horizon signed Stieltjes payout budget implies same-measure ENNReal payout budget
-- statement:
--   A genuine original Lévy process and dividend strategy, at exact ruin paymentTimes∩Iic T under actual dividendMeasure, has an integrable nonnegative real discounted payout factor. Any pathwise signed real Stieltjes integral upper bound by B transfers to an actual ENNReal lintegral upper bound by ENNReal.ofReal B with precisely identical measure and domain. Handles zero atom, continuous payments and horizon right-payment atom. No proxy random measure, missing finiteness or stochastic HJB assumption smuggled in.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal and ENNReal.ofReal_le_ofReal exact verified signature; original source definitions.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_exact_horizon_signed_cash_bound_to_ENNReal_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q T B : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω) ∩ Iic T)
      (dividendMeasure D ω))
    (hSigned :
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal B := by sorry
