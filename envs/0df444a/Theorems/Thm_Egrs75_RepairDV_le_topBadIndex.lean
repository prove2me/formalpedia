-- Prove2me | Theorems.Thm_Egrs75_RepairDV_le_topBadIndex
-- name    : Egrs75.RepairDV.le_topBadIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:00.358833+00:00
-- url     : https://prove2.me/theorems/7be1cd5f-ad78-4af3-8138-029f6ce4f430
-- title:
--   Repair DV: le top Bad Index
-- statement:
--   Maximality: every bad index is `≤ topBadIndex`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L170-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L170-L173

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction

theorem Egrs75.RepairDV.le_topBadIndex {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : i ∈ badIndexSet q n) : i ≤ topBadIndex q n := by sorry
