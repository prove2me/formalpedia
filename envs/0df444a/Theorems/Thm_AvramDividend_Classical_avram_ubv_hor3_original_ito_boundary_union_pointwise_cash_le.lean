-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:03:26.434635+00:00
-- url     : https://prove2.me/theorems/4e324da5-54e3-4686-9a5a-e33cd12afd9f
-- title:
--   All deterministic boundary faces of the original UBV natural-clock Itô budget, pointwise
-- statement:
--   For the original controlled Lévy source path, the exact discounted Stieltjes payout to horizon T through natural integer clip n is bounded by the initial HJB value whenever one of three genuine boundary conditions holds: n=0, T=0, or the original ruinTime is zero. All time-zero right payments are retained. This source lemma identifies the remaining pathwise interior n>0, T>0, ruinTime>0, which is the stochastic Itô–Meyer obligation; it does not assume or fake that interior estimate.
-- source:
--   Direct disjunction elimination over the three distinct original boundary faces. Import newly Proved/public n=0 all nonnegative horizons 05a6f562, already Proved all-n zero horizon d57573e3, and Proved all-n positive/nonnegative horizon immediate-ruin pointwise 8c661bc1. Use no FDB martingale source or canonical parent, avoiding cycles.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_n_all_horizon_pointwise_full_stieltjes_le
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_nT_stieltjes_pointwise_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
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
    (hBoundary : n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
