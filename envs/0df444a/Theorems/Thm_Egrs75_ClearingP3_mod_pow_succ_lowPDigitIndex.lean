-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_mod_pow_succ_lowPDigitIndex
-- name    : Egrs75.ClearingP3.mod_pow_succ_lowPDigitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:15.53959+00:00
-- url     : https://prove2.me/theorems/57b47385-a63e-48ba-8e80-4daedb459a33
-- title:
--   Clearing P3: mod pow succ low PDigit Index
-- statement:
--   For `n ≠ 0`, the low `(m+1)`-block of `n` (where `m = lowPDigitIndex p n`) is exactly
--   `a_m·p^m`, with `a_m = n/p^m % p` the lowest nonzero digit (digits below `m` are zero).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L261-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L261-L268

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

theorem Egrs75.ClearingP3.mod_pow_succ_lowPDigitIndex {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n + 1)
      = (n / p ^ (lowPDigitIndex p n) % p) * p ^ (lowPDigitIndex p n) := by sorry
