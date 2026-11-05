-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
-- name    : AvramDividend.Classical.avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:47:32.509602+00:00
-- url     : https://prove2.me/theorems/d088b7ce-e4f6-49b0-a279-761bf610a5b0
-- title:
--   Original positive-time strict stopped source budget implies signed closed Stieltjes cash and postpayment terminal budget
-- statement:
--   For the genuine original BV spectrally negative Lévy process, combine a source-exact strict-horizon pre-rightpayment expected cash/terminal inequality with the proved full and strict cash L1, the proved pre/postterminal joint L1 and the right-horizon secant budget. The exact original closed Stieltjes cash plus strict-survival post-rightpayment terminal expected sum is at most w(x). The strict prebudget is explicit, and remains a separate canonical proof obligation.
-- source:
--   Proved original strict cash L1 67a9c5bf, full cash L1 f97e4695, pre/post joint terminal L1 e88885b6, new horizon pathwise lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original strict stopped W/Cash/Term inequality, once established,
implies the exact closed-horizon signed terminal budget by L1 and hjump. -/

theorem AvramDividend.Classical.avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (hS : 0 < S)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hStrict :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω)
     else 0 ∂P) ≤ w x := by sorry
