-- Prove2me | solution 1 for section5_normalize_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:54.425383+00:00
-- url     : https://prove2.me/submissions/d5482df2-0777-4b98-bcc8-1d7589746ae2

import Mathlib
set_option autoImplicit false
theorem solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x-y‖ / ‖y‖ := by
  have hnx : ‖NormedSpace.normalize x‖ = 1 := NormedSpace.norm_normalize hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have heq : ‖y‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (‖y‖-‖x‖) • NormedSpace.normalize x + (x-y) := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  have hh := norm_add_le ((‖y‖-‖x‖) • NormedSpace.normalize x) (x-y)
  rw [← heq, norm_smul, Real.norm_of_nonneg (norm_nonneg y), norm_smul,
    Real.norm_eq_abs, hnx, mul_one] at hh
  have hl : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa [abs_sub_comm] using abs_norm_sub_norm_le x y
  apply (le_div_iff₀ hny).mpr
  nlinarith
