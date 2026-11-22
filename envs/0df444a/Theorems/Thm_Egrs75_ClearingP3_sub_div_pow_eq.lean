-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_div_pow_eq
-- name    : Egrs75.ClearingP3.sub_div_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:33.023156+00:00
-- url     : https://prove2.me/theorems/0b12a869-487e-4dae-bec4-bc54d0c4d121
-- title:
--   Clearing P3: sub div pow eq
-- statement:
--   The subtract keeps the same high base-`q` quotient: `(n - S) / q^j = n / q^j`, for
--   `S ≤ n % q^j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L346-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L346-L356

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

theorem Egrs75.ClearingP3.sub_div_pow_eq {q n S k : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ k) :
    (n - S) / q ^ k = n / q ^ k := by sorry
