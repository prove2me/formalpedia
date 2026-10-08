-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_admissible_hjb_jump_bound
-- name    : AvramDividend.Classical.local_verification_admissible_hjb_jump_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T07:19:03.016595+00:00
-- url     : https://prove2.me/theorems/3b129274-1d92-4fe2-ac4c-d4e73a274b5d
-- title:
--   Actual HJB hypotheses cover the right dividend jump at an admissible strategy payment time
-- statement:
--   For an admissible strategy D, at each active right dividend jump with reserve strictly inside cap C, the exact HJB smoothness and maximum assumptions of local_verification imply that the payout rightLimit D t−D t is no greater than the drop in the general verification function w. It combines the monotone dividend rightLimit, the admissibility reserve constraint, and the generic HJB value-drop lemma. This is a direct part of Proposition 4's singular control verification inequality.
-- source:
--   Children dividendStrategy_le_rightLimit and local_verification_hjb_controls_dividend_jump; exact mission IsAdmissible definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_admissible_hjb_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (huC : ENNReal.ofReal (riskProcess X x D t ω) < C) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by sorry
