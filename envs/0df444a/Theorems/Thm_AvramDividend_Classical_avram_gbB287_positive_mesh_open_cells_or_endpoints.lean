-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB287_positive_mesh_open_cells_or_endpoints
-- name    : AvramDividend.Classical.avram_gbB287_positive_mesh_open_cells_or_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:06:00.354211+00:00
-- url     : https://prove2.me/theorems/ef903375-4512-4184-b26b-1e5d37dbc78d
-- title:
--   Finite positive real mesh times lie in an open cell or finite boundary set
-- statement:
--   Every nonnegative time strictly below a positive finite real mesh horizon lies strictly inside a grid cell or equals a left endpoint in the finite boundary range. This refines the original Proved half-open cover B282 and supports omission of B283 measure-null endpoints in the original Gaussian occupation argument.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB287_positive_mesh_open_cells_or_endpoints (N : ℕ) (δ t : ℝ)
    (hδ : 0 < δ) (ht : 0 ≤ t) (horizon : t < (N : ℝ) * δ) :
    (∃ i : ℕ, i < N ∧
      t ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ)) ∨
    t ∈ Set.range (fun i : Fin N => (i : ℝ) * δ) := by sorry
