-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
-- name    : AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:07:40.304521+00:00
-- url     : https://prove2.me/theorems/3b331f7a-be78-4974-ad4a-192df1698b31
-- title:
--   Uniform bounded-horizon estimate for exact stopped physical generator mesh with true clipped NNReal cell widths
-- statement:
--   For the original stopped canonical physical mesh v_i=min(i/(j+1),rho), the actual discounted ℝ≥0 truncated cell widths and any uniformly bounded generator integrand F_i give |Q_j|≤nB at every mesh, provided the stopped clock rho≤n and q≥0. This exact-path source estimate helps establish integrability of localised generator Riemann terms and avoids silently changing NNReal cell subtraction to a different grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
    (q : ℝ) (hq : 0 ≤ q)
    (n j : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (B : ℝ) (hB : 0 ≤ B) (F : ℕ → ℝ)
    (hF : ∀ i < (n + 1) * (j + 1), |F i| ≤ B) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let m : ℕ := (n + 1) * (j + 1)
    |∑ i ∈ Finset.range m,
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (((v (i + 1) - v i : ℝ≥0) : ℝ)) * F i| ≤ (n : ℝ) * B := by sorry
