-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cap_overshoot_grid_envelope
-- name    : AvramDividend.Classical.avram_p3_bv_original_cap_overshoot_grid_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:00:18.412524+00:00
-- url     : https://prove2.me/theorems/7add1798-3fa6-4877-8868-9a49de8016bb
-- title:
--   Original BV jump-removed physical grid cap overshoot controlled by drift and true residual
-- statement:
--   On one original bounded-variation source probability-one event, for every ordered nonnegative time grid and every reserve input per cell, the sum of absolute finite-cap overshoot changes due to frozen jump-removed physical source increments is bounded by the physical source drift magnitude over elapsed time plus the true monotone raw-negative-jump-removed residual increment. This gives the stopped BV C1 mesh its exact physical source cap-contact variation envelope without assuming residual zero or source-frozen reserves under the cap.
-- source:
--   Composition of Proved original grid variation e9650890-8657-43f3-bf81-46f202f62ba6 and Proved finite-cap overshoot Lipschitz eb3d3c8c-0a80-4245-a78e-c635d1ecf0af. Bridge to Open source mesh db6a3111-3498-45ee-937e-060f93612dd2 requires stochastic integrability and limit passage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_overshoot_step_lipschitz

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_cap_overshoot_grid_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (c : ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (z : ℕ → ℝ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
            max (z i - c) 0|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by sorry
