-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_two_mul_half_pred
-- name    : Egrs75.ClearingP3.two_mul_half_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:04.421125+00:00
-- url     : https://prove2.me/theorems/9774517c-0444-4676-8d43-38a543ccbfb2
-- title:
--   Clearing P3: two mul half pred
-- statement:
--   `2 * ((p - 1) / 2) = p - 1` for odd `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L135-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L135-L137

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

theorem Egrs75.ClearingP3.two_mul_half_pred {p : ℕ} (hodd : Odd p) : 2 * ((p - 1) / 2) = p - 1 := by sorry
