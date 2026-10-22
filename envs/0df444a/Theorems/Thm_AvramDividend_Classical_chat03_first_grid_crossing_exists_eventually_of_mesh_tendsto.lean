-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
-- name    : AvramDividend.Classical.chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T13:57:56.912146+00:00
-- url     : https://prove2.me/theorems/61c1740a-427b-43f7-8a58-a7eb19f01b5e
-- title:
--   Vanishing meshes eventually detect the genuine first strict two-sided crossing
-- statement:
--   For any sample path of a spectrally negative Lévy process with a finite strict two-sided crossing infimum, every positive uniform-grid mesh sequence tending to zero eventually admits a minimal sampled strict crossing index. This follows from the accepted quantified mesh approximation theorem and does not impose a stochastic optional-stopping assumption.
-- source:
--   Corollary of the independently Proved Chat03 first strict grid exit approximation and convergence of mesh to zero.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ,
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by sorry
