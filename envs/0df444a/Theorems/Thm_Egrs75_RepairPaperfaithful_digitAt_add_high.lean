-- Prove2me | Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_high
-- name    : Egrs75.RepairPaperfaithful.digitAt_add_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:01.169212+00:00
-- url     : https://prove2.me/theorems/1d1c98d6-6aa4-47ce-b3a4-017bd776ccc8
-- title:
--   Repair Paperfaithful: digit At add high
-- statement:
--   For `k ≤ i` and `u < p^k`, the index-`i` base-`p` digit of `u + p^k * h` is the
--   index-`(i-k)` digit of `h` (the low block `u` is below `p^k`, so it does not reach
--   index `i ≥ k`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L97-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L97-L105

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

theorem Egrs75.RepairPaperfaithful.digitAt_add_high {p : ℕ} {k u h i : ℕ} (hu : u < p ^ k) (hki : k ≤ i) :
    digitAt p i (u + p ^ k * h) = digitAt p (i - k) h := by sorry
