-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_lowDigits_half_pred_pow
-- name    : Egrs75.ClearingP3.lowDigits_half_pred_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:13.572908+00:00
-- url     : https://prove2.me/theorems/7a53a550-b933-449e-8f5b-1879cc2ef959
-- title:
--   Clearing P3: low Digits half pred pow
-- statement:
--   **`LowDigits p ((p^m - 1)/2)`** — the half-repunit has every base-`p` digit equal to
--   `(p-1)/2`, hence all `≤ (p-1)/2`.  By induction on `m` via the recursion
--   `(p^(m+1)-1)/2 = p·((p^m-1)/2) + (p-1)/2` (a `lowDigits_cons`). KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L175-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L175-L181

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

theorem Egrs75.ClearingP3.lowDigits_half_pred_pow {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (m : ℕ) :
    LowDigits p ((p ^ m - 1) / 2) := by sorry
