-- Prove2me | Theorems.Thm_Egrs75_RepairDV_topBadIndex_mem
-- name    : Egrs75.RepairDV.topBadIndex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:09.381437+00:00
-- url     : https://prove2.me/theorems/c60a6fd2-437a-4fee-b65d-28756fa85b34
-- title:
--   Repair DV: top Bad Index mem
-- statement:
--   The top bad index is itself a bad index: its base-`q` digit is oversized and it is
--   within the digit list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L164-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L164-L167

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

theorem Egrs75.RepairDV.topBadIndex_mem {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n ∈ badIndexSet q n := by sorry
