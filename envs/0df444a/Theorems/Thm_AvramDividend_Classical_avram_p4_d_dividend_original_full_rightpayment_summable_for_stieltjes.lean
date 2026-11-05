-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_rightpayment_summable_for_stieltjes
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_rightpayment_summable_for_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:05:34.201885+00:00
-- url     : https://prove2.me/theorems/31ea0262-5089-4e3b-8dbc-833772ee3a62
-- title:
--   Actual full original Stieltjes right-payment secant remainder is summable automatically under local K
-- statement:
--   Discharge the exact full signed Stieltjes theorem summability obligation for the complete original positive pre-ruin rightpayment set through the closed horizon. Reconcile the accepted source x+X-rightLimit formulation to the canonical original post-Lévy-jump pre-dividend riskProcess minus right-dividend-increment formulation using the actual reserve definition. A local K upper secant bound is explicitly required, while time zero remains a distinct cap-linear term.
-- source:
--   Accepted source-exact cash absolute bound 1ced3e97 and the original riskProcess reserve identity by ring; exactly matches hSummable in d2232fa0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_rightpayment_summable_for_stieltjes
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
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ t : B,
      w (riskProcess X x D (t : ℝ≥0) ω) -
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) ≤
          K * (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) :
    Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) := by sorry
