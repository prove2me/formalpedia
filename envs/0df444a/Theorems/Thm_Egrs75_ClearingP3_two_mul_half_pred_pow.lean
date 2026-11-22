-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_two_mul_half_pred_pow
-- name    : Egrs75.ClearingP3.two_mul_half_pred_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:06.049695+00:00
-- url     : https://prove2.me/theorems/05f8ff1d-8150-4fbf-a6b7-0508ecde58b1
-- title:
--   Clearing P3: two mul half pred pow
-- statement:
--   `2 * ((p^m - 1)/2) = p^m - 1` (odd base ⟹ `p^m` odd ⟹ `p^m - 1` even).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L140-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L140-L144

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

theorem Egrs75.ClearingP3.two_mul_half_pred_pow {p : ℕ} (hodd : Odd p) (m : ℕ) :
    2 * ((p ^ m - 1) / 2) = p ^ m - 1 := by sorry
