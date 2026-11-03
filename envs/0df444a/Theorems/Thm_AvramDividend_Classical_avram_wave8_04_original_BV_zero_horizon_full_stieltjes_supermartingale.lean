-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_zero_horizon_full_stieltjes_supermartingale
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_zero_horizon_full_stieltjes_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:24:48.01402+00:00
-- url     : https://prove2.me/theorems/9e61982a-404b-4614-a9d4-131bebcbfc0b
-- title:
--   Original BV zero-horizon stopped verification with integrable survival terminal and complete rightpayment Stieltjes atom
-- statement:
--   The exact zero-horizon branch of the original BV stopped verification: both the full original time-zero Stieltjes dividend and the strict-survival post-rightpayment candidate value are integrable, and their real expectations sum to at most the initial verification candidate. Uses genuine original dividend measure and ruin time.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), Eq. (5.13), exact T=0 branch of 0618723a-bb0b-4fa0-94bc-4def7af7aafa. Reuses pre-existing proved expected time-zero budget with separately certified original terminal L1 and cash L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_strict_survival_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_zero_horizon_full_stieltjes_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
    let Term : Ω → ℝ := fun ω =>
      if (0 : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (w (x - rightLimit D 0 ω))
      else 0
    Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by sorry
