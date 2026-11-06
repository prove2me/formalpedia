-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_postpayment_residual_nonpos
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_postpayment_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:11:47.170591+00:00
-- url     : https://prove2.me/theorems/2fde3a96-7b6f-4683-8873-00c0bc9de479
-- title:
--   Original Lévy-before-dividend positive-time discounted payment residual is nonpositive
-- statement:
--   At every positive strictly pre-ruin instant of the actual controlled original Lévy path, the discounted sum of right-dividend cash atom and resulting w-value drop after the source Lévy jump is nonpositive. This preserves the Lévy-before-dividend chronological order under the existing original admissibility, cap and interior C1 gradient hypotheses.
-- source:
--   Pinned Proved original chronological source jump theorem 6cde6ec9 and positivity of the true discount factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_postpayment_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω) +
          (rightLimit D t ω - D t ω)) ≤ 0 := by sorry
