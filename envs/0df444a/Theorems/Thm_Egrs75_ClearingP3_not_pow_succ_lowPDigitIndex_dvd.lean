-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_not_pow_succ_lowPDigitIndex_dvd
-- name    : Egrs75.ClearingP3.not_pow_succ_lowPDigitIndex_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:01.637998+00:00
-- url     : https://prove2.me/theorems/deee15f3-faec-4232-9062-6e9a299236a1
-- title:
--   Clearing P3: not pow succ low PDigit Index dvd
-- statement:
--   For a prime `p` and `n ≠ 0`, `p ^ (lowPDigitIndex p n + 1) ∤ n` (the digit at
--   `m = lowPDigitIndex` is nonzero).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L97-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L97-L101

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

theorem Egrs75.ClearingP3.not_pow_succ_lowPDigitIndex_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ^ (lowPDigitIndex p n + 1) ∣ n := by sorry
