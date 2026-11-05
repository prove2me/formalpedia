-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
-- name    : AvramDividend.Classical.avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:38:30.380329+00:00
-- url     : https://prove2.me/theorems/ec5419c6-8d24-4405-98a1-45d6c5896cb9
-- title:
--   Source-exact BV all-horizon closed-cash/postpayment reward sharp upper bound, with correct singular zero-clock initial value
-- statement:
--   For the original bounded-variation Levy process and capped dividend strategy, the fully closed Stieltjes cash plus strict-survival post-rightpayment terminal is controlled by the strict cash plus prepayment terminal at every strictly positive horizon. At zero horizon it is controlled by the initial HJB value w(x), including the already-paid time-zero right atom even if ruin is immediate. Handles cap contact, ruin at T and no dividend double-counting with a single theorem and no artificial positive-clock assumption.
-- source:
--   Formal independent case split using the Proved positive-horizon literal original correction 3c21e5f9 and the source-exact G2 zero-clock atom inequality after its authoritative Proved/public receipt. No imports from canonical Open P3 residual, prebudget or signed budget.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (ω : Ω) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω)
     else 0) ≤
    (if S = 0 then w x
     else
       (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
        else 0)) := by sorry
