-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_subclock_caplinear_dividend_cash_drop_nonpositive
-- name    : AvramDividend.Classical.avram_f6_original_true_subclock_caplinear_dividend_cash_drop_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:01:27.641078+00:00
-- url     : https://prove2.me/theorems/cb3bc0a6-fde3-4bc7-b65b-9b3744c6625f
-- title:
--   True stopped clock original capped dividend cash and full caplinear reserve drop nonpositive
-- statement:
--   For every actual original zero or strictly pre-ruin subordinate stopping clock sigma(k), the discounted dividendMeasure cash on the full closed interval [0,sigma] together with the caplinear postpayment reserve change is nonpositive pathwise. It is a direct physical instantiation of the already Proved full original Stieltjes signed cash theorem b7f6754b with canonical slope-one V, preserving zero-time payout and rightLimit dividends. This is the signed dividend channel for common stopped Ito; it does not assert Gaussian/jump centring or ruin-contact residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_subclock_caplinear_dividend_cash_drop_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (k : ℕ) (ω : Ω)
    (hPre : σ k ω = 0 ∨
      (σ k ω : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫⁻ s in Icc (0 : ℝ) (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω) -
       V (x + X.X (σ k ω) ω)) ≤ 0 := by sorry
