-- Prove2me | Theorems.Thm_Egrs75_RepairDV_badCountQ_eq
-- name    : Egrs75.RepairDV.badCountQ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:09.015172+00:00
-- url     : https://prove2.me/theorems/d347ec92-a4d8-41fd-923c-8fb458d95bf1
-- title:
--   Repair DV: bad Count Q eq
-- statement:
--   `badCountQ` unfolded as a filter-length over the base-`q` digit list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L57-L58

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

theorem Egrs75.RepairDV.badCountQ_eq (q n : ℕ) :
    badCountQ q n = ((Nat.digits q n).filter (fun d => bigQ q d)).length := by sorry
