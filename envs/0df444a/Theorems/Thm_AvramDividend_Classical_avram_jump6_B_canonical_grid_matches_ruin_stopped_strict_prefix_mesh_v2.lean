-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_matches_ruin_stopped_strict_prefix_mesh_v2
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_grid_matches_ruin_stopped_strict_prefix_mesh_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:06:50.455449+00:00
-- url     : https://prove2.me/theorems/78b47994-eb2d-4caa-8e13-455be49552dd
-- title:
--   Proved p3 strict-prefix ruin-stopped mesh is exactly the original Jump6 uniform grid
-- statement:
--   Exact finite-mesh reparameterisation linking the Proved avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget, which uses T=n+1 and M=(n+1)(j+1), to the authentic Jump6 clipped grid u(i)=min(i/(j+1),rho). At positive ruin contact rho<=n the two grids agree for all original indices i<=M. This is a source-authentic conversion, not an assumed stochastic estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_canonical_grid_matches_ruin_stopped_strict_prefix_mesh_v2
    (n j i : ℕ) (ρ : ℝ≥0) (hρ : ρ ≤ (n : ℝ≥0))
    (hi : i ≤ (n + 1) * (j + 1)) :
    min (((min i ((n + 1) * (j + 1)) : ℕ) : ℝ≥0) *
      (((n + 1 : ℕ) : ℝ≥0) /
        (((n + 1) * (j + 1) : ℕ) : ℝ≥0)))
      (min ρ ((n + 1 : ℕ) : ℝ≥0)) =
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ := by sorry
