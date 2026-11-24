-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_eq_singleton
-- name    : BalanceSpecification.OneSidedExample.predecessor_probe_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:50:40.893801+00:00
-- url     : https://prove2.me/theorems/272e6163-e32b-4033-87f0-9edad73ef911
-- title:
--   One Sided Example: predecessor probe eq singleton
-- statement:
--   The One Sided Example construction uses the predecessor probe eq singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L304-L314
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L304-L314

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

theorem BalanceSpecification.OneSidedExample.predecessor_probe_eq_singleton {n : ℕ} (hn : 1 ≤ n) :
    predecessorFinset (language shift) (probeWord n) n = {List.replicate n a} := by sorry
