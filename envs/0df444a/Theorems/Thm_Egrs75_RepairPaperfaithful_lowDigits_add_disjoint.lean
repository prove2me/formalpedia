-- Prove2me | Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_add_disjoint
-- name    : Egrs75.RepairPaperfaithful.lowDigits_add_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:05.687754+00:00
-- url     : https://prove2.me/theorems/b5295647-3899-408e-8e62-39b3ac864a53
-- title:
--   Repair Paperfaithful: low Digits add disjoint
-- statement:
--   **Base-`p` safety.** If `u < p ^ k`, `LowDigits p u`, and `LowDigits p h`, then
--   `LowDigits p (u + p ^ k * h)`: the digit at each index is either a digit of `u`
--   (index `< k`) or a digit of `h` (index `≥ k`), all `≤ (p-1)/2`. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L115-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L115-L122

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

theorem Egrs75.RepairPaperfaithful.lowDigits_add_disjoint {p : ℕ} (hp : 2 ≤ p) {k u h : ℕ}
    (hu : u < p ^ k) (hlu : LowDigits p u) (hlh : LowDigits p h) :
    LowDigits p (u + p ^ k * h) := by sorry
