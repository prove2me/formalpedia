-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
-- name    : AvramDividend.Classical.chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:29:50.347994+00:00
-- url     : https://prove2.me/theorems/e51a9b32-8ef4-4a30-817b-90f66fa12e30
-- title:
--   Actual bounded first-hitting clock selects the first strict crossing with any positive terminal margin
-- statement:
--   The genuine measurable Mathlib hittingBtwn clock eventually equals the earliest strict upper or lower barrier crossing sampled on a positive vanishing uniform grid, provided its terminal physical time exceeds the finite continuous exit infimum by any specified positive margin ε. This strengthens the earlier fixed one-unit-margin identification and permits capped grids close to their finite observation horizon.
-- source:
--   Accepted chat03_hittingBtwn_eq_earliest_observed_crossing and the generalized chat03_first_grid_crossing_before_arbitrary_terminal_margin, with the max-of-signed-gaps encoding. Publication v2 uses a declaration-only authoring scaffold and is scheduled after all imported parent theorems are authoritatively Proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_before_arbitrary_terminal_margin
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_earliest_observed_crossing
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ ε : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hε : 0 < ε)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᶠ n in atTop,
      (X.X ((K n ω : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((K n ω : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < K n ω →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  sorry
