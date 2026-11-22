-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_half_pred_pow_lt
-- name    : Egrs75.ClearingP3.half_pred_pow_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:35.786455+00:00
-- url     : https://prove2.me/theorems/1603c546-f822-443f-b323-dcc478210d85
-- title:
--   Clearing P3: half pred pow lt
-- statement:
--   `(p^m - 1)/2 < p^m` (strict, since `(p^m - 1)/2 ≤ p^m - 1 < p^m`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L184-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L184-L187

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

theorem Egrs75.ClearingP3.half_pred_pow_lt {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : (p ^ m - 1) / 2 < p ^ m := by sorry
