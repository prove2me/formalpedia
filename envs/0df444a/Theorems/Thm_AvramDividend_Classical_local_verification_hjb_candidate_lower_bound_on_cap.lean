-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap
-- name    : AvramDividend.Classical.local_verification_hjb_candidate_lower_bound_on_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:24:41.424292+00:00
-- url     : https://prove2.me/theorems/42edbf80-4efe-4e9f-8604-888bdd6e458d
-- title:
--   HJB candidate is at least capital plus its initial value within the capped state domain
-- statement:
--   Under the exact smoothness, one-sided continuity, HJB gradient inequality and nonnegative w(0) assumptions of local verification, every real reserve y≥0 with ENNReal.ofReal y≤C satisfies w(y)≥w(0)+y≥0. Apply the already Proved local_verification_hjb_controls_dividend_jump_le_cap to a hypothetical dividend d=y paid from reserve u=y. The validated generic dividend secant inequality becomes y≤w(y)−w(0). Rearrange and use y≥0 and w(0)≥0. This is the nonnegative-terminal-residual condition needed in the stopped dividend verification argument. No stochastic integral or optional-stopping theorem is asserted.
-- source:
--   Derive from the authoritative Proved generic HJB dividend jump secant 2aa7e3a6-ad5d-4b97-bed1-618140a1fd71, with u=d=y.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_candidate_lower_bound_on_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    y + w 0 ≤ w y ∧ 0 ≤ w y := by sorry
