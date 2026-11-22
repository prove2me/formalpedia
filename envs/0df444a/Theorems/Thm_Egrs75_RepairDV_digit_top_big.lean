-- Prove2me | Theorems.Thm_Egrs75_RepairDV_digit_top_big
-- name    : Egrs75.RepairDV.digit_top_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:57.015696+00:00
-- url     : https://prove2.me/theorems/167a6c3f-dfd6-4578-a6a4-65303d5d4e1e
-- title:
--   Repair DV: digit top big
-- statement:
--   The base-`q` digit at index `topBadIndex q n` is itself oversized
--   (`(q-1)/2 < n / q^(topBadIndex) % q`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L228-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L228-L234

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

theorem Egrs75.RepairDV.digit_top_big {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 < n / q ^ (topBadIndex q n) % q := by sorry
