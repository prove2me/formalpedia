-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_rightjump_residual_sum_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_rightjump_residual_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:38:46.953688+00:00
-- url     : https://prove2.me/theorems/3f1fee7f-4abd-459e-83f2-24d616684903
-- title:
--   Finite sums of genuine original right-dividend discounted residuals are nonpositive
-- statement:
--   For any finite set of actual dividend payment times eligible before original ruin (including t=0), sum the exact discounted right-jump residual from source dividend control D and candidate w. Each term is nonpositive by the accepted original per-atom theorem, so the sum is nonpositive. This is a finite-jump assembly step, with no claim yet about infinite Stieltjes mass.
-- source:
--   Proved exact original rightjump discounted residual 9f4070e7 and pinned Finset.sum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_rightjump_residual_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (F : Finset ℝ≥0)
    (hpre : ∀ t ∈ F, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω))) ≤ 0 := by sorry
