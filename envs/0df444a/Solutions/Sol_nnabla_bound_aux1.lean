-- Prove2me | solution 1 for nnabla_bound_aux1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:39.107206+00:00
-- url     : https://prove2.me/submissions/358342ab-90ed-41d0-9eff-fb6483c7660b

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

theorem solution (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop := by
  have hdiv : Tendsto (fun x : ℝ => x / b) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hb).2 tendsto_id
  have hlog : Tendsto (fun x : ℝ => Real.log (x / b)) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hsq : Tendsto (fun x : ℝ => Real.log (x / b) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by decide)).comp hlog
  exact tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_left atTop a hsq)
