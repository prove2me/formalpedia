-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_shifted_mesh_exp_limit
-- name    : AvramDividend.Classical.avram_redux19_shifted_mesh_exp_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:26:28.173955+00:00
-- url     : https://prove2.me/theorems/1c987ea3-979a-43f9-afa3-b5607c1b6a1f
-- title:
--   Finite shifted n-cell linearised Laplace multiplier converges to the exponential
-- statement:
--   The n+1 finite-time-cell approximation with each cell linearised at 1-x/(n+1) converges to the exact Laplace exponential exp(-x), including all real x and zero x. The shifted mesh avoids the denominator zero at n=0.
-- source:
--   Instantiate the pinned Real.tendsto_one_add_div_pow_exp with -x, compose with the verified Filter.tendsto_add_atTop_nat 1, then normalise the natural-number cast and signs.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux19_shifted_mesh_exp_limit (x : ℝ) :
    Tendsto (fun n : ℕ =>
      (1 - x / ((n : ℝ) + 1)) ^ (n + 1)) atTop
      (𝓝 (Real.exp (-x))) := by sorry
