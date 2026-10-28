-- Prove2me | Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_of_bracketed_jump
-- name    : AvramDividend.Classical.downward_grid_limsup_of_bracketed_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:09:46.807559+00:00
-- url     : https://prove2.me/theorems/b2c051a1-39e8-4415-8adc-2785ff313c25
-- title:
--   Converging observation brackets detect a strict downward jump on arbitrarily fine grids
-- statement:
--   For a real-valued path with a strictly downward jump relative to a candidate left limit, suppose each finite observation grid contains a pair of times whose path values converge respectively to that left limit and the post-jump value. The path then belongs to the limsup grid event of strict downward increments beyond the specified threshold. This provides a deterministic jump-to-countable-cylinder bridge useful in identifying canonical Poisson jump counts from the càdlàg path.
-- source:
--   Convergence of subtraction in Filter.Tendsto and the open threshold neighbourhood Iio_mem_nhds, followed by eventual membership and finite-grid witness selection.

import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set
open scoped NNReal

theorem AvramDividend.Classical.downward_grid_limsup_of_bracketed_jump
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (s u : ℕ → ℝ≥0) (f : ℝ≥0 → ℝ)
    (t : ℝ≥0) (left a : ℝ)
    (hgrid : ∀ n, (s n, u n) ∈ grid n)
    (hs : Tendsto (fun n => f (s n)) atTop (nhds left))
    (hu : Tendsto (fun n => f (u n)) atTop (nhds (f t)))
    (hjump : f t - left < -a) :
    f ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {g : ℝ≥0 → ℝ | g ij.2 - g ij.1 < -a}) := by sorry
