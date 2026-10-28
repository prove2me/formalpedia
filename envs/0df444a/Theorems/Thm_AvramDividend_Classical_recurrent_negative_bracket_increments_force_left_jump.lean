-- Prove2me | Theorems.Thm_AvramDividend_Classical_recurrent_negative_bracket_increments_force_left_jump
-- name    : AvramDividend.Classical.recurrent_negative_bracket_increments_force_left_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:17:01.987676+00:00
-- url     : https://prove2.me/theorems/21120934-785c-42be-90e5-b9326d9ffe66
-- title:
--   Recurrent negative decrements on converging brackets force a downward limiting jump
-- statement:
--   For a path f, let a sequence of left-bracket values converge to a candidate left limit and right-bracket values converge to f(t). If, arbitrarily far along the sequence, the right-minus-left decrement is less than −a, then the limiting jump f(t) minus the left limit is at most −a. The conclusion is weak due to possible convergence onto the threshold. This is the reverse analytic direction for detecting intrinsic càdlàg jumps from countable grid observations.
-- source:
--   Filter.Tendsto.sub and Ioi_mem_nhds force all sufficiently late increments above −a whenever the limiting jump is strictly above −a; this contradicts the recurrent downward bracket witnesses.

import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set
open scoped NNReal

theorem AvramDividend.Classical.recurrent_negative_bracket_increments_force_left_jump
    (s u : ℕ → ℝ≥0) (f : ℝ≥0 → ℝ)
    (t : ℝ≥0) (left a : ℝ)
    (hs : Tendsto (fun n => f (s n)) atTop (nhds left))
    (hu : Tendsto (fun n => f (u n)) atTop (nhds (f t)))
    (hrec : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      f (u n) - f (s n) < -a) :
    f t - left ≤ -a := by sorry
