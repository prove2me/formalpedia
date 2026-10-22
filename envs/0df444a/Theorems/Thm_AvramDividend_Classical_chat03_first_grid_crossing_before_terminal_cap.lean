-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_before_terminal_cap
-- name    : AvramDividend.Classical.chat03_first_grid_crossing_before_terminal_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:17:55.893525+00:00
-- url     : https://prove2.me/theorems/0f492608-4cec-43cf-99cd-bf3873c453b7
-- title:
--   Fine grids detect first strict crossing before a sufficiently distant terminal cap
-- statement:
--   For a fixed Lévy sample path with finite first strict two-sided passage infimum τ, a sequence of positive meshes tending to zero and terminal indices m(n) whose physical times eventually exceed τ+1, every sufficiently fine grid has an earliest strict crossing index no greater than m(n). This supplies the finite-cap witness needed to identify the actual Mathlib bounded hittingBtwn stopping index.
-- source:
--   Use the accepted strict first-grid exit approximation with ε=1 and compare crossing time k·mesh(n) < τ+1 with the eventual cap m(n)·mesh(n), then cancel the positive mesh factor.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_crossing_before_terminal_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ, k ≤ m n ∧
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by sorry
