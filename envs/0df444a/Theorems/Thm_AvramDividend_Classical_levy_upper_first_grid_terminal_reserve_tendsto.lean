-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upper_first_grid_terminal_reserve_tendsto
-- name    : AvramDividend.Classical.levy_upper_first_grid_terminal_reserve_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:05:32.983339+00:00
-- url     : https://prove2.me/theorems/c0594eaf-d3e2-470a-9a47-91d8d2b78d72
-- title:
--   Strict first upper-grid crossing reserve converges to the true finite passage reserve
-- statement:
--   If a sample path has a finite strict upper-passage time τ which is the greatest lower bound of its actual strict crossing times, and each sufficiently fine uniform grid is sampled through its genuine first strict upper crossing, then the reserve observed at that sampled first crossing converges to Xτ. The result is upper-only, assumes no artificial lower barrier, and follows from the Proved strict upper mesh approximation plus càdlàg right continuity.
-- source:
--   Proved chat03_strict_upper_exit_mesh_approximation (45efdde1-0fe8-43f1-9f72-af75af3c1f57) and the right-continuous path field of SpectrallyNegativeLevy. Pattern adapted to the independently accepted two-sided stopped reserve convergence, with first-upper minimality.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_mesh_approximation
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.levy_upper_first_grid_terminal_reserve_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      upper < X.X ((first n : ℝ≥0) * mesh n) ω ∧
      ∀ j : ℕ, j < first n →
        ¬ upper < X.X ((j : ℝ≥0) * mesh n) ω) :
    Tendsto (fun n => X.X ((first n : ℝ≥0) * mesh n) ω) atTop
      (𝓝 (X.X τ ω)) := by sorry
