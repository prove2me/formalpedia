-- Prove2me | solution 1 for tendsto_mul_add_atTop
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:04.212206+00:00
-- url     : https://prove2.me/submissions/cb0c282d-60aa-4c8b-a83a-08100a7985bc

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Filter
open scoped Topology

theorem solution {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop := by
  exact (tendsto_id.const_mul_atTop ha).atTop_add tendsto_const_nhds
