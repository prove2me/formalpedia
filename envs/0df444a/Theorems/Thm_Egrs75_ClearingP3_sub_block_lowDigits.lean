-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_block_lowDigits
-- name    : Egrs75.ClearingP3.sub_block_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:14.689476+00:00
-- url     : https://prove2.me/theorems/d3587818-e2ed-41fc-8837-ba41ff0d792d
-- title:
--   Clearing P3: sub block low Digits
-- statement:
--   **The borrow block is `LowDigits p`.**  For `1 ≤ a ≤ (p-1)/2`, the block
--   `a·p^m - (p^m+1)/2` is `LowDigits p`: it equals `(a-1)·p^m + (p^m-1)/2`, whose digit at
--   `m` is `a-1 ≤ (p-1)/2` and whose digits below `m` are all `(p-1)/2`. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L214-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L214-L232

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

theorem Egrs75.ClearingP3.sub_block_lowDigits {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) {a m : ℕ}
    (ha1 : 1 ≤ a) (haA : a ≤ (p - 1) / 2) :
    LowDigits p (a * p ^ m - (p ^ m + 1) / 2) := by sorry
