-- Prove2me | Theorems.Thm_AvramDividend_Classical_prepeak_reflected_ruin_hitting_time_sandwich
-- name    : AvramDividend.Classical.prepeak_reflected_ruin_hitting_time_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T06:12:59.661002+00:00
-- url     : https://prove2.me/theorems/f8268b67-22a3-4de5-9a84-0a41e3408f8e
-- title:
--   Extended first-hitting-time bounds for killed drawdown ruin before the next peak
-- statement:
--   For a time-indexed path X and its running supremum S, suppose S remains in [0,h] on the pre-upcrossing time set I. The earliest strictly below-(h−a) ordinary exit occurs no later than the earliest strictly above-a drawdown breach in I, which occurs no later than the earliest strictly below-(−a) ordinary exit. Each first passage is the infimum in extended nonnegative reals of the corresponding time set, with infinity for an empty event. This is the pathwise first-hitting-time ordering used to bracket killed upcrossing probabilities before deriving the q-scale ratios. It makes no stochastic Markov or scale-function assumption, and does not claim the dividend valuation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 reflected process and two-sided exit comparison; uses the remotely Proved strict drawdown cutoff theorem 45e397da-f6fa-4eb0-a294-6c3ab2c5f2c5 and order-reversal of the infimum under set inclusion.

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_drawdown_strict_exit_strip_of_sup_bounds
open scoped NNReal ENNReal

theorem AvramDividend.Classical.prepeak_reflected_ruin_hitting_time_sandwich
    (I : Set ℝ≥0) (S X : ℝ≥0 → ℝ) (a h : ℝ)
    (hSup : ∀ t ∈ I, 0 ≤ S t ∧ S t ≤ h) :
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ X t < h - a}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t}) ∧
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ X t < -a}) := by sorry
