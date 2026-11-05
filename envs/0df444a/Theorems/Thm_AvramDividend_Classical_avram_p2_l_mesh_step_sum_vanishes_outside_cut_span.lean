-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
-- name    : AvramDividend.Classical.avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:48:40.635195+00:00
-- url     : https://prove2.me/theorems/210d24f5-4a1a-4b39-97e1-d73577b6eede
-- title:
--   Finite ordered half-open step sums vanish outside the first-to-last cut span
-- statement:
--   For any monotone finite sequence of real partition cuts and any real sample coefficients, the sum of half-open successor-interval indicators is zero to the left of the first cut (inclusive) and strictly to the right of the final cut. The left-open/right-closed endpoint conventions are essential and directly handle the compact-support tails in P2-L's global uniform step approximation.

import Mathlib

open Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
    {n : ℕ} (p : Fin (n + 1) → ℝ) (c : Fin n → ℝ)
    (hp : Monotone p) (z : ℝ)
    (hz : z ≤ p 0 ∨ p (Fin.last n) < z) :
    (∑ i : Fin n,
      if z ∈ Ioc (p i.castSucc) (p i.succ) then c i else 0) = 0 := by sorry
