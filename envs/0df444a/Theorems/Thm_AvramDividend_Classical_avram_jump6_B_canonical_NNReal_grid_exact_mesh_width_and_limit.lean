-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:09:47.685458+00:00
-- url     : https://prove2.me/theorems/c96b7658-6f3c-4b29-a7cd-af14979944f8
-- title:
--   True canonical NNReal physical time grid has reciprocal mesh width and vanishing real mesh
-- statement:
--   For the actual fixed physical canonical grid u(j,i)=i/(j+1) in nonnegative reals, each real cell step is exactly 1/(j+1) and tends to zero as j grows. Supplies the exact mesh-width premise to the already Proved original closed-Iic clipped Stieltjes cash estimate for all caps and strict pre-ruin stopped clocks.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    (∀ j i, (u j (i + 1) : ℝ) - (u j i : ℝ) =
       (1 : ℝ) / ((j : ℝ) + 1)) ∧
    Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by sorry
