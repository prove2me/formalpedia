-- Prove2me | Theorems.Thm_BalanceSpecification_exists_sparse_marker_sequence
-- name    : BalanceSpecification.exists_sparse_marker_sequence
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:12.304042+00:00
-- url     : https://prove2.me/theorems/0e3851fe-50d2-4c1c-8156-43ec97ec01cc
-- title:
--   Balance Specification: exists sparse marker sequence
-- statement:
--   The explicit source-compatible sparse sequence `s_n = D * 4^n` can be
--   chosen to grow by more than a factor two and have total weighted pressure at
--   most one half. The entropy base here is `ρ²`; the marker base is `ρ > 1`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L40-L105
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L40-L105

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.exists_sparse_marker_sequence {ρ C : ℝ} (hρ : 1 < ρ) (hC : 1 ≤ C) (M : ℕ) :
    ∃ D : ℕ, 0 < D ∧
      (∀ n : ℕ, 2 * (D * 4 ^ n) < D * 4 ^ (n + 1)) ∧
      (∀ n : ℕ, 4 * (n + M) ≤ D * 4 ^ n) ∧
      (∀ N : ℕ, (∑ n ∈ Finset.range N,
        if 1 ≤ n then C * (ρ ^ 2) ^ n / ρ ^ (D * 4 ^ n + 1) else 0) ≤ 1 / 2) ∧
      (∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ D * 4 ^ n) := by sorry
