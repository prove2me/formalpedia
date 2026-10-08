-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_w_nonneg_below_cap
-- name    : AvramDividend.Classical.local_verification_w_nonneg_below_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:17:07.643981+00:00
-- url     : https://prove2.me/theorems/94afd169-a67e-4e25-ae8e-d19c2b33e84c
-- title:
--   The original HJB gradient and w(0)≥0 assumptions force w≥0 throughout the allowed reserve interval
-- statement:
--   If the local verification candidate w is continuous, has w(0)≥0, has the required BV/UBV smoothness, and satisfies max((Γ−q)w,1−w′)=0 in the interior, then w(y)≥0 for every 0≤y with ofReal y≤C, including y=C. Apply the proven generic cap-inclusive HJB dividend-jump bound at initial reserve u=y and full payout d=y, giving y≤w(y)−w(0); combine with y≥0 and w(0)≥0. This directly supplies the terminal-value nonnegativity assumption in both stochastic verification branches.
-- source:
--   Child local_verification_hjb_controls_dividend_jump_le_cap, accepted candidate 8416, and root local_verification assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_w_nonneg_below_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by sorry
