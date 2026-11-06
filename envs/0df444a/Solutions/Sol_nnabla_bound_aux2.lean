-- Prove2me | solution 1 for nnabla_bound_aux2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:53.007409+00:00
-- url     : https://prove2.me/submissions/415c27d4-3e18-4912-b644-21501f8ea755

import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit true
open Real Filter
open scoped Topology

theorem solution (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) := by
  have hdiv : Tendsto (fun x : ℝ => x / b) atTop atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_id.atTop_mul_const (inv_pos.mpr hb))
  have hlog : Tendsto (fun x : ℝ => Real.log (x / b)) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hsq : Tendsto (fun x : ℝ => Real.log (x / b) ^ 2) atTop atTop := by
    simpa [pow_two] using hlog.atTop_mul_atTop₀ hlog
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hsq.eventually (eventually_gt_atTop (-a))] with x hx hsq_x
  exact mul_pos hx (by linarith)
