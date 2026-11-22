-- Prove2me | Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_low
-- name    : Egrs75.RepairPaperfaithful.digitAt_add_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:12.864955+00:00
-- url     : https://prove2.me/theorems/6951e5a0-3424-4449-b622-adb22b94c542
-- title:
--   Repair Paperfaithful: digit At add low
-- statement:
--   For `i < k`, the index-`i` base-`p` digit of `u + p^k * h` is the digit of `u`
--   (the high block `p^k * h` contributes nothing below index `k`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L82-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L82-L92

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction

theorem Egrs75.RepairPaperfaithful.digitAt_add_low {p : ℕ} (hp : 1 ≤ p) {k u h i : ℕ} (hik : i < k) :
    digitAt p i (u + p ^ k * h) = digitAt p i u := by sorry
