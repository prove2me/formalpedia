-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_card_box_double
-- name    : Auto.aux_ErgodicBox.card_box_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:57.166317+00:00
-- url     : https://prove2.me/theorems/6ef222a4-abca-4f3c-b90a-429ed4c06a93
-- title:
--   aux Ergodic Box: card box double
-- statement:
--   The aux Ergodic Box construction uses the card box double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2446-L2449
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2446-L2449

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

theorem Auto.aux_ErgodicBox.card_box_double (n M : ℕ) :
    (box n (M + M)).card = 2 ^ n * (box n M).card := by sorry
