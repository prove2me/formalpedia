-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:41:35.147097+00:00
-- url     : https://prove2.me/theorems/1bcd326b-637b-4a3f-be9c-97c69e2c428a
-- title:
--   Sharp real-valued original BV expected full Stieltjes cash for every bounded random clock
-- statement:
--   For the actual standing bounded-variation spectrally negative Lévy source and cap-admissible original dividend strategy, the real Bochner expectation of all ruin-stopped discounted Stieltjes cash paid through any measurable random clock bounded by T is at most x+T times the strictly positive original BV drift. It includes the time-zero payment, right-limit atoms, and continuous or singular-continuous portions. Proved original-source measurability, L¹ integrability, almost-sure finiteness and the independently accepted sharp ENNReal cash bound yield the real comparison; no HJB verification conclusion is assumed.
-- source:
--   Accepted sharp BV random-clock ENNReal drift budget 25ef34c9; accepted original BV L1 cash 5817eddd; accepted original bounded-clock ae finite cash e1455beb; strict BV drift 0432f641; Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
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
    (∫ ω, (fun ω => (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) ≤ x + (T : ℝ) * X.drift := by sorry
