-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_digit_at_lowPDigitIndex_pos
-- name    : Egrs75.ClearingP3.digit_at_lowPDigitIndex_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:04.839947+00:00
-- url     : https://prove2.me/theorems/676c0cc3-35c5-4f34-94e3-847e5843069f
-- title:
--   Clearing P3: digit at low PDigit Index pos
-- statement:
--   The base-`p` digit of `n` at the lowest-nonzero index `m` is nonzero:
--   `0 < n / p^m % p`.  (From `p^m ∣ n` and `p^(m+1) ∤ n`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L105-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L105-L124

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

theorem Egrs75.ClearingP3.digit_at_lowPDigitIndex_pos {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    0 < n / p ^ (lowPDigitIndex p n) % p := by sorry
