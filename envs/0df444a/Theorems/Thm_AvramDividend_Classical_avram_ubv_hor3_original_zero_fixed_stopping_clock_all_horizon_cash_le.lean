-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_fixed_stopping_clock_all_horizon_cash_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_fixed_stopping_clock_all_horizon_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:13:25.223656+00:00
-- url     : https://prove2.me/theorems/9e2869d6-4cda-419c-884a-530675b116b5
-- title:
--   Literal zero stopped clock original UBV full Stieltjes cash bound for every nonnegative deterministic horizon
-- statement:
--   For the source original controlled Lévy process, a literally zero stopped clock restricts dividendMeasure to its single time-zero atom. At any nonnegative deterministic horizon this raw Stieltjes payout remains controlled by the source HJB value w(x), with no assumption on the original stochastic martingale and no special natural-ruin clock construction.
-- source:
--   Use Proved source paymentTimes_min_zero_eq_singleton_zero (77cdd573) with σ=0 to identify paymentTimes 0={0}; for T≥0 the two intersection clocks with Iic T and Iic 0 are exactly equal. Apply the public Proved arbitrary clock zero-horizon source HJB pointwise result 651ba069. This is an independent literal-zero auxiliary clock needed in source stopping/localisation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_fixed_stopping_clock_all_horizon_cash_le
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
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (∫⁻ t in paymentTimes (0 : ℝ≥0∞) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
