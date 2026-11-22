-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_preserves_lowDigits
-- name    : Egrs75.ClearingP3.sub_preserves_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:34.51148+00:00
-- url     : https://prove2.me/theorems/de3faa1d-0f31-4b06-8c91-6465e1bb109a
-- title:
--   Clearing P3: sub preserves low Digits
-- statement:
--   **Base-`p` safety of `n - (p^m+1)/2`.**  For odd prime `p`, a `LowDigits p` number
--   `n ≠ 0` with lowest nonzero base-`p` digit at `m = lowPDigitIndex p n`, the SUBTRACT
--   result `n - (p^m+1)/2` is `LowDigits p`.
--
--   The borrow is confined to the low `(m+1)`-block: `n = a_m·p^m + p^(m+1)·Hi` with
--   `Hi = n/p^(m+1)` (`LowDigits p`, untouched) and `a_m·p^m = n % p^(m+1)` the only block
--   the subtraction touches.  Since `(p^m+1)/2 ≤ a_m·p^m` (as `a_m ≥ 1`), the result is
--   `(a_m·p^m - (p^m+1)/2) + p^(m+1)·Hi`, and the low block is `LowDigits p` and `< p^(m+1)`
--   by `sub_block_lowDigits` / `sub_block_lt`; the disjoint sum is `LowDigits p` by the
--   proven adder `RepairDV.lowDigits_disjoint_add`.  KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L282-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L282-L335

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

theorem Egrs75.ClearingP3.sub_preserves_lowDigits {p : ℕ} (hp : p.Prime) (hodd : Odd p) {n : ℕ}
    (hpn : LowDigits p n) (hn : n ≠ 0) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) := by sorry
