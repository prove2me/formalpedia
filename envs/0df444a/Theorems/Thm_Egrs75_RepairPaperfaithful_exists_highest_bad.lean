-- Prove2me | Theorems.Thm_Egrs75_RepairPaperfaithful_exists_highest_bad
-- name    : Egrs75.RepairPaperfaithful.exists_highest_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:07.190732+00:00
-- url     : https://prove2.me/theorems/f25143fb-7d33-474f-98ef-db7a84701af9
-- title:
--   Repair Paperfaithful: exists highest bad
-- statement:
--   If `badCountQ q n > 0` then some base-`q` digit index is bad, and there is a
--   greatest such index. (Bad indices are bounded by the length of the digit list, so
--   the nonempty bounded set of bad indices has a maximum.) KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L136-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L136-L172

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

theorem Egrs75.RepairPaperfaithful.exists_highest_bad {q n : ℕ} (hq : 2 ≤ q) (hbad : 0 < badCountQ q n) :
    ∃ j, BadAt q j n ∧ ∀ i, BadAt q i n → i ≤ j := by sorry
