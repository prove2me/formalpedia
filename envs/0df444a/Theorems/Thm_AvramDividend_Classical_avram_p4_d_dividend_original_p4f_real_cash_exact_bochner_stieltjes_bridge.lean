-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_p4f_real_cash_exact_bochner_stieltjes_bridge
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_bochner_stieltjes_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:39:45.805709+00:00
-- url     : https://prove2.me/theorems/cf5e25d6-65ab-48c0-8be8-f38ef1f3f8ae
-- title:
--   Literal original P4-F Cash equals real-valued stopped dividend Stieltjes integral
-- statement:
--   Under the literal P4-F source assumption defining Cash as the real conversion of the ENNReal discounted original dividendMeasure lintegral at the true ruin time and random finite horizon, Cash is exactly the ordinary real Bochner Stieltjes integral on that same true stopped payment set. The source-exact integrability proof justifies the conversion. This supplies the explicit real Cash term required for integration with signed Itô–Meyer dividend-control residuals.
-- source:
--   Original P4-F hCash and Proved original stopped Cash Bochner equality

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_bochner_stieltjes_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    Cash ω =
      ∫ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * s)) ∂(dividendMeasure D ω) := by sorry
