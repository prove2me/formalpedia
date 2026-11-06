-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_n_all_horizon_pointwise_full_stieltjes_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_n_all_horizon_pointwise_full_stieltjes_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:48:38.968915+00:00
-- url     : https://prove2.me/theorems/05a6f562-7be3-45c9-bda8-d0445893dfe3
-- title:
--   Zero finite-ruin truncation original Stieltjes payout HJB pointwise budget for every nonnegative horizon
-- statement:
--   For every original controlled Lévy sample path and any nonnegative horizon T, the exact raw dividendMeasure Stieltjes cash paid before the zero natural ruin-clock truncation is bounded by ENNReal.ofReal(w x). Unlike the known expected n=0 theorem, this source result is pointwise, preserves the 0-time right-payment atom and assumes neither immediate ruin nor any stochastic finite-grid martingale.
-- source:
--   Proved paymentTimes_min_zero_eq_singleton_zero 77cdd573 shows zero clip pays only at t=0; for T≥0 its full closed horizon set equals the closed zero horizon set. Apply newly Proved/public source all-n zero-horizon pointwise bound d57573e3 with n=0, using no stochastic source witness.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_n_all_horizon_pointwise_full_stieltjes_le
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
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
