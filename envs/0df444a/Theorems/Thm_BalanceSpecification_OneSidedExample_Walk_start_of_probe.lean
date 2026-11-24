-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_start_of_probe
-- name    : BalanceSpecification.OneSidedExample.Walk.start_of_probe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:43.322041+00:00
-- url     : https://prove2.me/theorems/a947e75c-d2dc-4579-95cb-1fa1161052a3
-- title:
--   Walk: start of probe
-- statement:
--   Reading `ab^(n+1)` requires an upper starting vertex high enough to have
--   `n` incoming `a` steps; a lower starting vertex is impossible for positive `n`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L260-L277
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L260-L277

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.Walk.start_of_probe {n : ℕ} (hn : 1 ≤ n) {s t : Vertex}
    (h : Walk s (a :: List.replicate (n + 1) b) t) :
    ∃ k : ℕ, s = .q k ∧ n ≤ k + 1 := by sorry
