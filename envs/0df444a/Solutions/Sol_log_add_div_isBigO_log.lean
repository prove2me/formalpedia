-- Prove2me | solution 1 for log_add_div_isBigO_log
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:31.105927+00:00
-- url     : https://prove2.me/submissions/6270f91c-627c-45a8-bdbd-0686cbbc6206

import Mathlib.Analysis.SumIntegralComparisons

open Real Filter Asymptotics

theorem solution (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  have hdiff : (fun x : ℝ ↦ Real.log (x + a) - Real.log x) =O[atTop] Real.log :=
    ((Real.tendsto_log_comp_add_sub_log a).isBigO_one ℝ).trans
      Real.isLittleO_const_log_atTop.isBigO
  have hconst : (fun _ : ℝ ↦ Real.log b) =O[atTop] Real.log :=
    Real.isLittleO_const_log_atTop.isBigO
  have hmain := (hdiff.add (Asymptotics.isBigO_refl Real.log atTop)).sub hconst
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (-a)] with x hx
  have hxa : x + a ≠ 0 := by linarith
  rw [Real.log_div hxa (ne_of_gt hb)]
  ring
