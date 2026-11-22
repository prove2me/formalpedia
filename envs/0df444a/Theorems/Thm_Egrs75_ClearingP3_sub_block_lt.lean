-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_block_lt
-- name    : Egrs75.ClearingP3.sub_block_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:19.490107+00:00
-- url     : https://prove2.me/theorems/26582f7e-66a2-45e1-b09a-74a0bc4b34e9
-- title:
--   Clearing P3: sub block lt
-- statement:
--   The borrow block stays below `p^(m+1)`: `a·p^m - (p^m+1)/2 < p^(m+1)`
--   (for `1 ≤ a ≤ (p-1)/2`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L236-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L236-L255

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

theorem Egrs75.ClearingP3.sub_block_lt {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) {a m : ℕ}
    (ha1 : 1 ≤ a) (haA : a ≤ (p - 1) / 2) :
    a * p ^ m - (p ^ m + 1) / 2 < p ^ (m + 1) := by sorry
