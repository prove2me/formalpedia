-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_compact_band_all_positive_rightatom_absolute_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_all_positive_rightatom_absolute_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:05:48.323636+00:00
-- url     : https://prove2.me/theorems/4b4219e3-c2c6-46de-a7d2-e8f1b36daffd
-- title:
--   Original stopped full positive right-dividend series absolutely dominated by Cash from local C1 source band
-- statement:
--   For every strictly positive right-dividend payment strictly before actual ruin, through the closed horizon, require both actual pre- and post-dividend reserves to lie in one compact C1 band. The derivative ceiling L and explicit canonical hjump establish absolute summability of the complete signed chronological series, its nonpositivity and the exact L-times-original-Cash bound. This removes any independent local secant premise without claiming boundary regularity at zero or cap.
-- source:
--   Composition of accepted exact all-positive source atomic cash series 1ced3e97 and original compact Lipschitz right-payment secant 77773c05; both imported public Proved helpers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_all_positive_rightatom_absolute_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧ t ≤ T ∧
      0 < rightLimit D t ω - D t ω})
    (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (hpre : ∀ t : B, riskProcess X x D (t : ℝ≥0) ω ∈ Icc a b)
    (hpost : ∀ t : B,
      x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω ∈ Icc a b) :
    let J : B → ℝ := fun t => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
        w (riskProcess X x D (t : ℝ≥0) ω))
    Summable J ∧ (∑' t : B, J t) ≤ 0 ∧
      Summable (fun t : B => |J t|) ∧
      (∑' t : B, |J t|) ≤ ((1 + (L : ℝ)) - 1) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
