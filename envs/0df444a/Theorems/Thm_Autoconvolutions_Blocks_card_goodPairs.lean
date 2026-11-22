-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_card_goodPairs
-- name    : Autoconvolutions.Blocks.card_goodPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:32.492335+00:00
-- url     : https://prove2.me/theorems/bfa911a3-582d-47b4-b170-9e2ef1cd8f86
-- title:
--   Blocks: card good Pairs
-- statement:
--   The Blocks construction uses the card good Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L57-L59
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L57-L59

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_Autoconvolutions_Occupancy
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]

theorem Autoconvolutions.Blocks.card_goodPairs (I J : Finset ι) (u v : ℕ) :
    ((goodVectors I u) ×ˢ (goodVectors J v)).card = I.card.choose u * J.card.choose v := by sorry
