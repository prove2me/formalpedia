-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_high_digits_frozen
-- name    : Egrs75.ClearingP3.sub_high_digits_frozen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:37.078414+00:00
-- url     : https://prove2.me/theorems/471c08bc-ff24-4a71-95e9-a489412c11af
-- title:
--   Clearing P3: sub high digits frozen
-- statement:
--   **Base-`q` digits at index `≥ j` are frozen.**  For `S ≤ n % q^j`, every base-`q`
--   digit of `n - S` at index `idx ≥ j` equals the corresponding digit of `n`. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L361-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L361-L368

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

theorem Egrs75.ClearingP3.sub_high_digits_frozen {q n S j idx : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ j)
    (hidx : j ≤ idx) :
    (n - S) / q ^ idx % q = n / q ^ idx % q := by sorry
