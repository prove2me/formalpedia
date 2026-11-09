-- Prove2me | solution 1 for e7_exp_neg_scale_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:54:40.267263+00:00
-- url     : https://prove2.me/submissions/e8deb7b1-2eae-4394-9850-0c95d75b10f9

import Mathlib

theorem solution (rate : ℝ) (hrate : 0 < rate) :
    Filter.Tendsto (fun T : ℝ => Real.exp (-rate * T)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun T : ℝ => rate * T) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hrate Filter.tendsto_id
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  simpa [neg_mul, Function.comp_def] using h
