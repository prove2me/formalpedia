-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_card_goodVectors
-- name    : Autoconvolutions.Blocks.card_goodVectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:29.853266+00:00
-- url     : https://prove2.me/theorems/44d2fb9b-d496-4c21-9c11-13fafea79698
-- title:
--   Blocks: card good Vectors
-- statement:
--   The Blocks construction uses the card good Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L36-L37
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L36-L37

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

theorem Autoconvolutions.Blocks.card_goodVectors (I : Finset ι) (k : ℕ) :
    (goodVectors I k).card = I.card.choose k := by sorry
