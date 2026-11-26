-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_card_box
-- name    : Auto.aux_ErgodicBox.card_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:26.51056+00:00
-- url     : https://prove2.me/theorems/fa2006fb-93eb-41e8-84c0-c79c48e6613f
-- title:
--   aux Ergodic Box: card box
-- statement:
--   The aux Ergodic Box construction uses the card box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2436-L2437
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2436-L2437

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.card_box (n L : ℕ) : (box n L).card = L ^ n := by sorry
