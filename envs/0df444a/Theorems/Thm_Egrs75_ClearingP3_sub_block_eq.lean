-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_block_eq
-- name    : Egrs75.ClearingP3.sub_block_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:38.208729+00:00
-- url     : https://prove2.me/theorems/78df2d32-8533-4930-b024-077755f0e747
-- title:
--   Clearing P3: sub block eq
-- statement:
--   The borrow identity: for `1 ≤ a`, `a·p^m - (p^m+1)/2 = (a-1)·p^m + (p^m-1)/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L192-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L192-L209

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP3.sub_block_eq {p : ℕ} (hodd : Odd p) {a m : ℕ} (ha : 1 ≤ a) :
    a * p ^ m - (p ^ m + 1) / 2 = (a - 1) * p ^ m + (p ^ m - 1) / 2 := by sorry
