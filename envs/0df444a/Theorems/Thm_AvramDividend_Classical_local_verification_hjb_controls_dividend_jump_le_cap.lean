-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
-- name    : AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:21:33.083069+00:00
-- url     : https://prove2.me/theorems/2aa7e3a6-ad5d-4b97-bed1-618140a1fd71
-- title:
--   Generic HJB gradient bounds dividend jumps even when the reserve is exactly at the cap
-- statement:
--   Under the exact HJB and C¹/C² assumptions of local_verification, any dividend 0≤d≤u from a reserve satisfying ofReal u≤C is bounded by the loss w(u)−w(u−d), including the boundary case ofReal u=C. The derivative only needs to be at interior points z strictly below u, which remain strictly below cap by strict monotonicity of ofReal at z≥0. This removes the previous unnecessary strict-cap restriction on the generic dividend jump verification inequality.
-- source:
--   Children local_verification_smooth_differentiable, local_verification_hjb_implies_components, derivative_ge_one_implies_value_drop; Mathlib ENNReal.ofReal_lt_ofReal_iff_of_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap
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
    (huC : ENNReal.ofReal u ≤ C) :
    d ≤ w u - w (u - d) := by sorry
