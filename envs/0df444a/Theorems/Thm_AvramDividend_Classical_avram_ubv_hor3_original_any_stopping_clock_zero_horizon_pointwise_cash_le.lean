-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:55:38.469337+00:00
-- url     : https://prove2.me/theorems/651ba069-b87d-4dd9-8f4b-f7dce333c965
-- title:
--   Any original source stopping clock zero-horizon full Stieltjes payout bounded pointwise by HJB value
-- statement:
--   For the original controlled Lévy process, the exact source dividendMeasure cash paid to the closed horizon zero is bounded pointwise by ENNReal.ofReal(w x) for every arbitrary extended-nonnegative source stopping clock σ, independent of natural ruin, integer truncation or the stopped Brownian/jump martingale representation. It preserves the complete time-zero right-payment atom and is stronger than the natural all-n zero-horizon boundary.
-- source:
--   Directly combine Proved source zero-horizon Stieltjes = original dividendMeasure singleton 1fb597ac, valid for any σ:ENNReal, with newly Proved/public original samplewise initial right atom HJB bound 1794a9b8. No proxy law, original source martingale integration or canonical parent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
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
    (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
