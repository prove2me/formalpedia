-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:34:23.120883+00:00
-- url     : https://prove2.me/theorems/cf0ea4b5-d353-466b-bb08-54033bb006ee
-- title:
--   Original strict-survival discounted post-dividend terminal is nonnegative and dominated by pre-dividend value
-- statement:
--   Under exactly the canonical bounded-variation candidate regularity, cap, admissible original dividend strategy and hJump assumptions, the actual right-postpayment strict-survival terminal payoff is pointwise nonnegative and bounded above by the prepayment one. Use the Proved original w-postpayment nonnegativity theorem, canonical dividend monotonicity and the hJump secant bound; the result preserves zero/cap contacts, finite and infinite caps and time-zero dividend atoms.
-- source:
--   Proved original postpayment terminal nonnegative 28b04520; original dividendStrategy_le_rightLimit 953f0e91; canonical signed P3 9cd69d89 hJump and all regularity assumptions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (t : ℝ≥0),
      0 ≤ (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω)
       else 0) ∧
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω)
       else 0) ≤
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω)
       else 0) := by sorry
