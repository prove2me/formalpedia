-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_follower_card_lower_bound
-- name    : BalanceSpecification.OneSidedExample.follower_card_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:49:52.820799+00:00
-- url     : https://prove2.me/theorems/2134875c-0283-4288-9488-8c5ae633d0f7
-- title:
--   One Sided Example: follower card lower bound
-- statement:
--   Binary outgoing choices at any terminal vertex give distinct followers.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L189-L198
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L189-L198

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

theorem BalanceSpecification.OneSidedExample.follower_card_lower_bound {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    2 ^ n ≤ (followerFinset (language shift) u n).card := by sorry
