-- Prove2me | Theorems.Thm_Egrs75_ClearingP2_lowDigits_div_pow
-- name    : Egrs75.ClearingP2.lowDigits_div_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:02.153171+00:00
-- url     : https://prove2.me/theorems/4fdd2bbd-5d19-4f65-8e55-da0dfa5b1fe8
-- title:
--   Clearing P2: low Digits div pow
-- statement:
--   **High base-`p` block stays low (KERNEL-CLEAN).**  If every base-`p` digit of `n`
--   is `≤ (p-1)/2`, so is every base-`p` digit of `n / p^m`: the digit of `n / p^m` at
--   index `i` is the digit of `n` at index `m + i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L84-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L84-L93

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP2.lowDigits_div_pow {p : ℕ} (hp : 2 ≤ p) {n m : ℕ}
    (hpn : LowDigits p n) : LowDigits p (n / p ^ m) := by sorry
