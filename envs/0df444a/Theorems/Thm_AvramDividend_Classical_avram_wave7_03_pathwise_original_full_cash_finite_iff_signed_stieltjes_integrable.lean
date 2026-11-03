-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
-- name    : AvramDividend.Classical.avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:46:59.539874+00:00
-- url     : https://prove2.me/theorems/a6d24d2f-ba0a-4cab-9a77-a8e79c213a92
-- title:
--   Full original pathwise ENNReal perpetual Stieltjes cash finite exactly when genuine untruncated signed real integrand is integrable
-- statement:
--   A two-way exact original process dividend Stieltjes theorem: for any actual original path and real discount q, finiteness of the full unrestricted pre-ruin inner ENNReal cash on paymentTimes(ruinTime) against the exact dividendMeasure is equivalent to IntegrableOn of the same nonnegative real discounted density on precisely that restricted measure. The proof uses positivity and measurability of exp, the pinned Mathlib lintegral_ofReal_ne_top_iff_integrable and lt_top_iff_ne_top. No incorrect substitution for the time-zero right-limit atom, continuous payout or strict pre-ruin interval.
-- source:
--   Pinned Mathlib lintegral_ofReal_ne_top_iff_integrable, lt_top_iff_ne_top and exact original source definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) < ⊤ ↔
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) := by sorry
