-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_subset
-- name    : BalanceSpecification.OneSidedExample.predecessor_probe_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:49:39.486912+00:00
-- url     : https://prove2.me/theorems/a770ec70-778d-4f54-bfbe-7c1ee319a7d7
-- title:
--   One Sided Example: predecessor probe subset
-- statement:
--   The complete predecessor set is contained in the singleton asserted by the source.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L290-L298
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L290-L298

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

theorem BalanceSpecification.OneSidedExample.predecessor_probe_subset {n : ℕ} (hn : 1 ≤ n) :
    predecessorFinset (language shift) (probeWord n) n ⊆ {List.replicate n a} := by sorry
