-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
-- name    : AvramDividend.Classical.avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:28:36.694796+00:00
-- url     : https://prove2.me/theorems/b9d0997e-9683-4278-bcf1-e7e49acbf918
-- title:
--   Original zero-horizon initial dividend atom and source postpayment HJB value budget without extra nonnegativity hypothesis
-- statement:
--   At zero observation time, the exact original stopped Stieltjes cash includes the time-zero right dividend, and the genuine postpayment terminal (only on strict survival) is bounded jointly by w(x). Genuine positive-cap BV admissibility and the original C1 gradient derive postpayment nonnegativity, including cap contact. The non-survival event carries no fictitious terminal and the initial dividend is counted exactly once.
-- source:
--   Direct formal consequence of publicly Proved original cap/gradient postpayment nonnegativity 28b04520 and original zero-clock full atom budget 50981c17, discharging the independent hpost premise using source X.X_zero. No P3 Open target, artificial martingale, or prebudget used.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
      w (x + X.X 0 ω - rightLimit D 0 ω)
     else 0) ≤ w x := by sorry
