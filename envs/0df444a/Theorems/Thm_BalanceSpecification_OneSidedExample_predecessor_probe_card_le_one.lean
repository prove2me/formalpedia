-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_card_le_one
-- name    : BalanceSpecification.OneSidedExample.predecessor_probe_card_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:50.730809+00:00
-- url     : https://prove2.me/theorems/c34e08dc-b1da-43b1-9485-89e1dd7ba3b9
-- title:
--   One Sided Example: predecessor probe card le one
-- statement:
--   The One Sided Example construction uses the predecessor probe card le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L300-L302
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L300-L302

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

theorem BalanceSpecification.OneSidedExample.predecessor_probe_card_le_one {n : ℕ} (hn : 1 ≤ n) :
    (predecessorFinset (language shift) (probeWord n) n).card ≤ 1 := by sorry
