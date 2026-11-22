-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_half_pred_pow_succ
-- name    : Egrs75.ClearingP3.half_pred_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:15.962617+00:00
-- url     : https://prove2.me/theorems/851eee76-0ced-4084-917b-d7caf56034f2
-- title:
--   Clearing P3: half pred pow succ
-- statement:
--   The recursion for the half-repunit: `(p^(m+1) - 1)/2 = p · ((p^m - 1)/2) + (p-1)/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L148-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L148-L170

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

theorem Egrs75.ClearingP3.half_pred_pow_succ {p : ℕ} (hp : 2 ≤ p) (hodd : Odd p) (m : ℕ) :
    (p ^ (m + 1) - 1) / 2 = p * ((p ^ m - 1) / 2) + (p - 1) / 2 := by sorry
