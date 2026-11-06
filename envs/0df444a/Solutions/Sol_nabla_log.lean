-- Prove2me | solution 1 for nabla_log
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:39.571203+00:00
-- url     : https://prove2.me/submissions/6f8202d5-4e31-4440-8c9a-2eb6d090e8c2

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open Real Filter Asymptotics

set_option autoImplicit true

theorem solution {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hdiv : Real.log ((x + 1) / b) - Real.log (x / b) = Real.log (1 + 1 / x) := by
    rw [← Real.log_div (div_ne_zero (by linarith) hb.ne') (div_ne_zero hx.ne' hb.ne')]
    congr 1
    field_simp
  change ‖Real.log ((x + 1) / b) - Real.log (x / b)‖ ≤ 1 * ‖1 / x‖
  calc
    _ = Real.log (1 + 1 / x) := by
      rw [hdiv, Real.norm_eq_abs, abs_of_nonneg]
      apply Real.log_nonneg
      have hx' : 0 ≤ 1 / x := (one_div_pos.mpr hx).le
      linarith
    _ ≤ 1 / x := by
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity)
      linarith
    _ = 1 * ‖1 / x‖ := by
      rw [one_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hx)]
