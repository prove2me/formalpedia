-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b236_discounted_original_continuous_stieltjes_finite_mesh_cash_terminal_value_budget
-- name    : AvramDividend.Classical.avram_b236_discounted_original_continuous_stieltjes_finite_mesh_cash_terminal_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:31:37.578248+00:00
-- url     : https://prove2.me/theorems/9ad344e0-c3e7-4487-ac32-2c7b0573d882
-- title:
--   Original physical monotone-time discounted finite continuous dividend cash plus terminal candidate value bounded by initial value
-- statement:
--   For the actual pre-ruin physical ordered time mesh t_0≤...≤t_n, nonnegative discount rate q, a nonnegative candidate reserve-value sequence V_i≥0 and real continuous/right-dividend cash increments cash_i satisfying cash_i≤V_i−V_{i+1} on each physical cell (as supplied by original w′≥1 reserve secant or exact right-payment HJB value-loss inequality), prove the exact DISCOUNTED Stieltjes bound ∑_{i<n}e^(−q t_i)cash_i + e^(−q t_n)V_n ≤ e^(−q t_0)V_0. Each clock discount decreases; multiplying the cash bound by its positive discount and using V_{i+1}≥0 gives a pointwise telescoping difference of discounted candidate values. Sum over the finite original physical mesh. This mathematical source piece directly isolates the continuous/right-dividend Stieltjes cash and terminal value budget in the true original B236 ruin-clipped Itô ledger, including time-zero payments if represented as an initial cell, without silently deleting the negative ruin-contact mark or assuming ν=0. The actual Ito Gaussian/marked stochastic cells, physical cash-to-partition matching and ruin terminal contact remain separate nontrivial obligations.
-- source:
--   Exact finite discounted summation by parts of nonnegative original pre-ruin candidate values and same-source reserve dividend inequalities.

import Mathlib
open Set Filter Topology MeasureTheory
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b236_discounted_original_continuous_stieltjes_finite_mesh_cash_terminal_value_budget
    (q : ℝ) (hq : 0 ≤ q)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (V cash : ℕ → ℝ) (n : ℕ)
    (hV : ∀ i ≤ n, 0 ≤ V i)
    (hCash : ∀ i < n, cash i ≤ V i - V (i + 1)) :
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (t i : ℝ))) * cash i) +
      Real.exp (-(q * (t n : ℝ))) * V n ≤
        Real.exp (-(q * (t 0 : ℝ))) * V 0 := by sorry
