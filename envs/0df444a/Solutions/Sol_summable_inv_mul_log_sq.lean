-- Prove2me | solution 1 for summable_inv_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:53.109803+00:00
-- url     : https://prove2.me/submissions/f41a8d7b-081d-4f8c-8570-32776f7a5045

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real
open Set MeasureTheory

theorem solution : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  apply AntitoneOn.summable_of_integrableOn_Ioi
    (f := fun x : ℝ => (x * (Real.log x) ^ 2)⁻¹) (N := 2)
  · intro x hx y hy hxy
    have hx2 : (2 : ℝ) ≤ x := hx
    have hy2 : (2 : ℝ) ≤ y := hy
    have hxpos : 0 < x := by linarith
    have hypos : 0 < y := by linarith
    have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hylog : 0 < Real.log y := Real.log_pos (by linarith)
    have hlog : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
    have hprod : x * (Real.log x) ^ 2 ≤ y * (Real.log y) ^ 2 := by
      gcongr
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hprod
  · simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
      (integrableOn_inv_div_log_sq_Ioi (c := (2 : ℝ)) (by norm_num))
  · intro t ht
    have ht1 : (1 : ℝ) < t := lt_trans (by norm_num) ht
    have htpos : 0 < t := by linarith
    have htlog : 0 < Real.log t := Real.log_pos ht1
    positivity
