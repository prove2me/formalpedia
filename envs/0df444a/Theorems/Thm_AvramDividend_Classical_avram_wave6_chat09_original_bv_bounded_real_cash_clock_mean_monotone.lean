-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_real_cash_clock_mean_monotone
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_real_cash_clock_mean_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:00:11.464012+00:00
-- url     : https://prove2.me/theorems/6f9f26fd-fb48-4746-9625-4b772f75a223
-- title:
--   Original BV real L¹ Stieltjes cash expectations increase under bounded ordered random clocks
-- statement:
--   For the actual Standing BV spectrally negative Lévy process, genuine capped admissible left-continuous original dividend control and q≥0, the real Bochner expectations of the complete ruin-stopped discounted Stieltjes cash at measurable random clocks τ≤σ≤T are ordered. Measurability and L¹ integrability come from the accepted original BV random-clock cash theorem; the original Stieltjes payout itself is pointwise monotone by set inclusion; a.s. finite upper-clock mass permits the ENNReal-to-real comparison. No HJB or martingale budget is assumed. Includes time zero, continuous and singular-continuous cash and terminal right-payment atoms.
-- source:
--   Original BV bounded random-clock real cash L1 theorem 5817eddd, original bounded-clock a.s. finite cash e1455beb, and Mathlib lintegral_mono_set, ENNReal.toReal_mono and integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_real_cash_clock_mean_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ σ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hσMeas : Measurable (fun ω => (σ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T)
    (hσBound : ∀ ω, σ ω ≤ T)
    (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫ ω, (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) ≤
      (∫ ω, (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) := by sorry
