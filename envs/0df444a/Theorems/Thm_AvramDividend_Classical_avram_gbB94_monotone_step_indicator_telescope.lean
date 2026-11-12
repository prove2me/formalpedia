-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB94_monotone_step_indicator_telescope
-- name    : AvramDividend.Classical.avram_gbB94_monotone_step_indicator_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:54:42.19372+00:00
-- url     : https://prove2.me/theorems/1aa11d82-72c3-4809-926e-24188d01d9c6
-- title:
--   Monotone half-open grid indicators telescope as endpoint steps
-- statement:
--   For any nondecreasing real grid, a sum of consecutive half-open cell indicators equals the difference of the two endpoint Heaviside indicators. This provides the cancellation identity needed to partition each original uniform Gaussian coarse cell into product-grid subcells in B93/B82.

import Mathlib
open Filter Topology
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB94_monotone_step_indicator_telescope
    (f : ℕ → ℝ) (hf : Monotone f)
    (t : ℝ) (N : ℕ) :
    (Finset.range N).sum (fun j =>
      if f j ≤ t ∧ t < f (j + 1) then (1 : ℝ) else 0) =
    (if f 0 ≤ t then (1 : ℝ) else 0) -
      (if f N ≤ t then (1 : ℝ) else 0) := by sorry
