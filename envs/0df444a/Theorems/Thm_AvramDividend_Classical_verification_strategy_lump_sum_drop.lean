-- Prove2me | Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
-- name    : AvramDividend.Classical.verification_strategy_lump_sum_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:48:17.699008+00:00
-- url     : https://prove2.me/theorems/a1e9aef9-1aee-4a1b-9795-4d4d88928e47
-- title:
--   Admissible dividend jumps are dominated by the verification-function drop
-- statement:
--   For any admissible capped strategy, every dividend right-jump that is constrained by admissibility, including the lump sum at time zero, is no larger than the corresponding decrease of a verification candidate satisfying w'≥1 on the capped positive domain. Monotonicity of D makes the jump nonnegative, admissibility ensures the post-dividend reserve is nonnegative, and the cap is supplied by the strategy for t>0 or by the initial-capital hypothesis at t=0.
-- source:
--   Deterministic jump-control component of the proof of Proposition 4(i), Avram–Palmowski–Pistorius (2007), Section 5.4. Uses the formal admissibility convention and verification_candidate_capped_lump_sum_drop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_verification_candidate_capped_lump_sum_drop

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.verification_strategy_lump_sum_drop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by sorry
