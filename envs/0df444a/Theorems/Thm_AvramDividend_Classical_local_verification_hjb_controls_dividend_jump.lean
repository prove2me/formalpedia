-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump
-- name    : AvramDividend.Classical.local_verification_hjb_controls_dividend_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:16:46.824345+00:00
-- url     : https://prove2.me/theorems/06d902ed-2fa5-402d-9d33-fc31b13590bf
-- title:
--   The actual Proposition 4 HJB and BV/UBV regularity hypotheses bound a generic dividend jump by w's value loss
-- statement:
--   Under the exact smoothness and max-equals-zero HJB assumptions of Proposition 4(i), any feasible dividend amount 0≤d≤u paid from an interior reserve u<C decreases the candidate verification function by at least d: d≤w(u)−w(u−d). The proof combines BV/UBV interior differentiability, HJB derivative≥1, and a mean-value-theorem estimate on [u−d,u]. This is the generic dividend-jump inequality for arbitrary local verification test functions, not merely the exponential special case.
-- source:
--   Children local_verification_smooth_differentiable, local_verification_hjb_implies_components, derivative_ge_one_implies_value_drop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_controls_dividend_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℝ) (hd : 0 ≤ d) (hcap : d ≤ u)
    (huC : ENNReal.ofReal u < C) :
    d ≤ w u - w (u - d) := by sorry
