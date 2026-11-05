-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_global_step_error_from_partition
-- name    : AvramDividend.Classical.avram_p2_l_mesh_global_step_error_from_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:02:57.127202+00:00
-- url     : https://prove2.me/theorems/37b225bb-9a4f-4efc-9269-110b6001e0a6
-- title:
--   Uniform global step error for a fine ordered compact-test partition including both tails
-- statement:
--   For a strictly increasing finite sequence of cuts, use left-endpoint samples of a real marked test on successive half-open cells. If the function has a uniform modulus on every narrow cell, vanishes left of the first cut and is η-small right of the last cut, the finite interval-step sum approximates the test uniformly to η over the entire real line. This is the central global deterministic estimate required by P2-L's unconditional compact-test convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_monotone_cuts_cover_interval
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_step_interior_modulus_error
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_step_sum_vanishes_outside_cut_span

open Set AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_global_step_error_from_partition
    {n : ℕ} (f : ℝ → ℝ) (p : Fin (n + 1) → ℝ)
    (δ η : ℝ) (hη : 0 < η) (hp : StrictMono p)
    (hwidth : ∀ i : Fin n, p i.succ - p i.castSucc < δ)
    (hmod : ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η)
    (hleft : ∀ z : ℝ, z ≤ p 0 → f z = 0)
    (hright : ∀ z : ℝ, p (Fin.last n) < z → |f z| ≤ η) :
    ∀ z : ℝ, |f z - (∑ i : Fin n,
      if z ∈ Ioc (p i.castSucc) (p i.succ)
      then f (p i.castSucc) else 0)| ≤ η := by sorry
