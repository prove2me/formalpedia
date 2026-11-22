-- Prove2me | Theorems.Thm_Egrs75_RepairDV_digit_good_above_top
-- name    : Egrs75.RepairDV.digit_good_above_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:02.967008+00:00
-- url     : https://prove2.me/theorems/64cd1650-7c85-4ca1-87c9-77ae3e25c163
-- title:
--   Repair DV: digit good above top
-- statement:
--   The base-`q` digit of `n` at any index strictly above `topBadIndex q n` is good
--   (`≤ (q-1)/2`).  Indices beyond the list read as `0` (also good); indices in range
--   above the top bad index are good by maximality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L184-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L184-L200

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction

theorem Egrs75.RepairDV.digit_good_above_top {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : topBadIndex q n < i) : n / q ^ i % q ≤ (q - 1) / 2 := by sorry
