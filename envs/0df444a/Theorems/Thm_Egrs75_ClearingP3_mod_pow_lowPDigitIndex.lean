-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_mod_pow_lowPDigitIndex
-- name    : Egrs75.ClearingP3.mod_pow_lowPDigitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:25.269525+00:00
-- url     : https://prove2.me/theorems/d5280190-2229-4fbf-94e8-0e3a088667fd
-- title:
--   Clearing P3: mod pow low PDigit Index
-- statement:
--   Below the lowest-nonzero index `m`, the base-`p` low block vanishes:
--   `n % p^m = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L128-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L128-L130

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

theorem Egrs75.ClearingP3.mod_pow_lowPDigitIndex {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n) = 0 := by sorry
