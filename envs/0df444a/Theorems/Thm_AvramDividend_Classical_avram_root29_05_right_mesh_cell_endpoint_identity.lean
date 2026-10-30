-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_cell_endpoint_identity
-- name    : AvramDividend.Classical.avram_root29_05_right_mesh_cell_endpoint_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:33:28.390205+00:00
-- url     : https://prove2.me/theorems/69f7fe98-3946-481f-b180-de46d676b28f
-- title:
--   Right-ceiling payment time is constant on each half-open uniform rational cell
-- statement:
--   For any denominator n+1, cell k and payment r strictly after its left endpoint and at most its right endpoint, the first right-mesh time ceil(r(n+1))/(n+1) equals exactly the cell's right endpoint (k+1)/(n+1). This exact half-open partition identity, including its upper endpoint, makes the Fatou mesh-weight integrand constant on each actual Stieltjes-measure cell and allows conversion into a sum of discounted record increments.
-- source:
--   Pinned Mathlib Int.ceil_eq_iff, div_lt_iff₀, le_div_iff₀ and natural cast arithmetic. Genuinely used by the positive-time killed Stieltjes cell-to-grid reconstruction for 79978d61.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

open Set
open scoped Classical

theorem AvramDividend.Classical.avram_root29_05_right_mesh_cell_endpoint_identity
    (n k : ℕ) (r : ℝ)
    (hr : r ∈ Ioc ((k : ℝ) / ((n : ℝ) + 1))
      (((k : ℝ) + 1) / ((n : ℝ) + 1))) :
    ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1) =
      ((k : ℝ) + 1) / ((n : ℝ) + 1) := by sorry
