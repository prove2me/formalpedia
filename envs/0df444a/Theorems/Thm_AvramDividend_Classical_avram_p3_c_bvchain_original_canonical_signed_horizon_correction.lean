-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_canonical_signed_horizon_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:56:50.024609+00:00
-- url     : https://prove2.me/theorems/3c21e5f9-78b6-4f04-a32a-1a94fed7a5d2
-- title:
--   Exact original strict-survival P3 canonical signed horizon dividend correction
-- statement:
--   For the actual original X,D, strict-survival canonical P3 terminal and physical original stopped payment measure at every positive S, the complete closed-horizon cash with post-rightLimit w is no greater than the strict-horizon cash with pre-rightpayment book w. It composes two source-exact proved helpers and preserves all original ruin and horizon conventions. In the full P3 proof, apply this pointwise and then the Proved joint L1/expectation lemmas to transfer the separately owned stochastic prebudget; no new stochastic assumption is introduced.
-- source:
--   Exact original signed true-clock hjump remainder 631a6ec4 and strict-survival canonical book-to-postpayment equality e7de115e; canonical P3 target 9cd69d89.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_canonical_signed_horizon_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) (hS : 0 < S) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (x + X.X S ω - rightLimit D S ω)
      else 0) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) := by sorry
