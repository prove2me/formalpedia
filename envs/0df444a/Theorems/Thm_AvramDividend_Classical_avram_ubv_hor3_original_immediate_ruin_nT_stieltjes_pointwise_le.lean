-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_nT_stieltjes_pointwise_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_nT_stieltjes_pointwise_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:04.258026+00:00
-- url     : https://prove2.me/theorems/8c661bc1-7091-4c4f-90ef-47141f02a322
-- title:
--   Original true immediate ruin finite-horizon Stieltjes payout bounded pointwise by HJB value
-- statement:
--   For the original controlled Lévy process and capped admissible dividends, on every sample path with immediate ruin, the complete raw ENNReal dividendMeasure payout to any nonnegative time horizon through any finite natural clip is bounded by ENNReal.ofReal(w x) using exactly the source HJB right-payment gradient/jump condition. This is pointwise rather than an expectation bound, handles the zero-time right-payment atom, and requires no stopped martingale decomposition.
-- source:
--   Proved original clipped immediate ruin raw cash identity f3f1ae05 (must first be Proved/public), already Proved original zero-clock pointwise cash upper 88f472ea, source zero-clock real Cash atom 5514c6b0, original singleton dividendMeasure 4f229f9a and dividend right-limit nonnegative. Instantiate exact auxiliary clock tau=0 and source W/Cash/Term definition, then convert finite initial atom mass and apply ofReal monotonicity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_clipped_closed_cash_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_nT_stieltjes_pointwise_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (ω : Ω)
    (hRuinZero : ruinTime X x D ω = 0) :
    (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
