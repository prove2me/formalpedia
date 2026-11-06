-- Prove2me | solution 1 for log_isbigo_log_div
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:58.812203+00:00
-- url     : https://prove2.me/submissions/9a242e27-bf23-481a-8273-53dff598c69d

import Mathlib.NumberTheory.Chebyshev

open Real Filter Asymptotics

theorem solution {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  have hdiv : Tendsto (fun x : ℝ ↦ x / d) atTop atTop :=
    Tendsto.atTop_div_const hb tendsto_id
  have h := (Real.isBigO_log_const_mul_log_atTop d).comp_tendsto hdiv
  simp only [Function.comp_def] at h
  have heq : (fun x : ℝ ↦ Real.log (d * (x / d))) = (fun n ↦ Real.log n) := by
    funext n
    congr 1
    field_simp
  rwa [← heq]
