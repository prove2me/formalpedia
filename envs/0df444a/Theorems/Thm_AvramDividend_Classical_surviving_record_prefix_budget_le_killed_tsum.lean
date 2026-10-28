-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_record_prefix_budget_le_killed_tsum
-- name    : AvramDividend.Classical.surviving_record_prefix_budget_le_killed_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:27:23.156508+00:00
-- url     : https://prove2.me/theorems/91b5e9bf-163e-4c82-aa31-4fa98f861e87
-- title:
--   Surviving finite record-prefix rewards are bounded by the killed infinite grid sum
-- statement:
--   For any monotone extended record clocks c, their finite real representatives u through index N, and a stopping horizon after record N, the sum of N+1 initial-record discounted h-payments is at most the countable sum of killed record payments. Each finite-prefix term survives the stopping test, matches its actual extended clock, and the finite prefix is dominated by the ENNReal infinite sum. This supplies the final pathwise algebraic step from finite-horizon Stieltjes cell budgets to the killed renewal weights used in the original upper-bound theorem.
-- source:
--   Use equality of finite record clocks with their NNReal representatives, monotone survival through index N, ENNReal.ofReal_mul, and ENNReal.tsum_eq_iSup_nat.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.surviving_record_prefix_budget_le_killed_tsum (τ : ℝ≥0∞) (q h : ℝ) (hh : 0 ≤ h)
    (c : ℕ → ℝ≥0∞) (u : ℕ → ℝ≥0) (N : ℕ)
    (hc : ∀ k : ℕ, k ≤ N → c k = (u k : ℝ≥0∞))
    (hmono : ∀ k : ℕ, k ≤ N → c k ≤ c N)
    (hSurvive : (u N : ℝ≥0∞) < τ) :
    (∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
        ENNReal.ofReal h) ≤
    (∑' k : ℕ,
      if c k < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * (c k).toReal)))
      else 0) := by sorry
