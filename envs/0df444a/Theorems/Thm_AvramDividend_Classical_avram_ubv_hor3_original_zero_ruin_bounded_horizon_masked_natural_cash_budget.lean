-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_natural_cash_budget
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_natural_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:13.606248+00:00
-- url     : https://prove2.me/theorems/8e9fb6a0-c03d-475b-8582-7ba6bc6f4695
-- title:
--   Original natural zero-ruin finite-horizon masked Stieltjes value with no auxiliary witnesses
-- statement:
--   The exact original bounded ruin-clock finite-horizon discounted dividendMeasure payout, restricted to the immediate-ruin event, is at most that event's initial HJB value in ENNReal expectation. The statement uses only the original X, x, capped admissible D and w/q, with no auxiliary stopped cash, terminal, stochastic or clock witness arguments. It preserves initial right-payment mass for every nonnegative horizon T and positive integer n.
-- source:
--   After 8c5aee33 is Proved and public, construct the true measurable and stopping ruin clock from Proved bbfbecf4 and 2d036d4f, obtain physical finite truncation d499e28b and original stopped W,Cash,Term witnesses 4a50bbff, apply the raw zero-clock bounded-horizon source bound 8c5aee33 and rewrite hτEq. This is an independent source-exact zero-event branch, no FDB or P4F3 dependency.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_natural_cash_budget
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
    (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 then
      (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 then
      ENNReal.ofReal (w x) else 0 ∂P) := by sorry
