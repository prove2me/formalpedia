-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_mem_box
-- name    : Auto.aux_ErgodicBox.mem_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:12.321209+00:00
-- url     : https://prove2.me/theorems/1e0c677d-d90f-5305-941a-76e5721ec36b
-- title:
--   aux Ergodic Box: mem box
-- statement:
--   The aux Ergodic Box construction uses the mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2432-L2434
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2432-L2434

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

theorem Auto.aux_ErgodicBox.mem_box {n L : ℕ} (k : Fin n → ℕ) :
    k ∈ box n L ↔ ∀ i, k i < L := by sorry
