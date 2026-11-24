-- Prove2me | Theorems.Thm_BalanceSpecification_exists_bounded_gap_beta_digits
-- name    : BalanceSpecification.exists_bounded_gap_beta_digits
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:35.865156+00:00
-- url     : https://prove2.me/theorems/9cb5a940-4dff-45b3-aa10-c5bdd6d49dae
-- title:
--   Balance Specification: exists bounded gap beta digits
-- statement:
--   Every residual strictly between zero and the full binary geometric sum has
--   an expansion with a uniform bound on the distance to the next digit one.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L131-L165
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L131-L165

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.exists_bounded_gap_beta_digits {β x : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2)
    (hx : 0 < x) (hxB : x < 1 / (β - 1)) :
    ∃ d : ℕ → ℝ, (∀ n, d n = 0 ∨ d n = 1) ∧
      (∃ N : ℕ, ∀ t : ℕ, ∃ s : ℕ, t ≤ s ∧ s ≤ t + N ∧ d s = 1) ∧
      HasSum (fun n : ℕ => d n / β ^ (n + 1)) x := by sorry
