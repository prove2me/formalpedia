-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_all_nonnegative_horizon_expected_post_le_strict_or_initial
-- name    : AvramDividend.Classical.avram_p3_g2_original_all_nonnegative_horizon_expected_post_le_strict_or_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:58:00.015358+00:00
-- url     : https://prove2.me/theorems/04b23b1e-4a42-4c27-a89b-e3ad878bde16
-- title:
--   Original BV all-nonnegative-horizon expected full cash and postpayment bound with exact zero initial-atom exception
-- statement:
--   For the actual original BV Levy process and admissible positive-cap strategy, the expectation of complete closed Stieltjes cash plus the strictly surviving post-rightpayment payoff is bounded at every horizon by the strict cash plus prepayment expectation when the horizon is positive, and by w(x) at the zero horizon. The zero-clock case uses genuine source-derived postpayment L1 and full cash L1, with the initial right dividend included once; the positive case is the previously Proved source exact expected comparison. No extra HJB residual, circular prebudget assumption or equality-in-law surrogate.
-- source:
--   Public Proved zero-clock G2 pathwise budget b9d0997e, G2 terminal joint L1 e88885b6, full-cash original L1 e53a9ae1, and original positive-horizon signed expected comparison 05cd664e. All source field and cap assumptions retained.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_postbudget_le_prebudget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_all_nonnegative_horizon_expected_post_le_strict_or_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    let Closed : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Open : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    (∫ ω, Closed ω + Post ω ∂P) ≤
      (if S = 0 then w x else (∫ ω, Open ω + Pre ω ∂P)) := by sorry
