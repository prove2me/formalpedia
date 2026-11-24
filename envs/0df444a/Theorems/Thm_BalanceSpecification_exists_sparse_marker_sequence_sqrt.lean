-- Prove2me | Theorems.Thm_BalanceSpecification_exists_sparse_marker_sequence_sqrt
-- name    : BalanceSpecification.exists_sparse_marker_sequence_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:01.550822+00:00
-- url     : https://prove2.me/theorems/c45527e4-eb5d-41e1-880c-69c84e2fe836
-- title:
--   Balance Specification: exists sparse marker sequence sqrt
-- statement:
--   Direct specialization to the square-root marker base used in the source
--   construction's entropy estimates.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L109-L120
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L109-L120

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

theorem BalanceSpecification.exists_sparse_marker_sequence_sqrt {β C : ℝ} (hβ : 1 < β)
    (hC : 1 ≤ C) (M : ℕ) :
    ∃ D : ℕ, 0 < D ∧
      (∀ n : ℕ, 2 * (D * 4 ^ n) < D * 4 ^ (n + 1)) ∧
      (∀ n : ℕ, 4 * (n + M) ≤ D * 4 ^ n) ∧
      (∀ N : ℕ, (∑ n ∈ Finset.range N,
        if 1 ≤ n then C * β ^ n / (Real.sqrt β) ^ (D * 4 ^ n + 1) else 0) ≤ 1 / 2) ∧
      (∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ D * 4 ^ n) := by sorry
