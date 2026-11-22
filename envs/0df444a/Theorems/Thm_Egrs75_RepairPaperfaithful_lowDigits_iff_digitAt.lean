-- Prove2me | Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt
-- name    : Egrs75.RepairPaperfaithful.lowDigits_iff_digitAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:01.982085+00:00
-- url     : https://prove2.me/theorems/196f1541-2968-4821-b96f-7836f8c19f0c
-- title:
--   Repair Paperfaithful: low Digits iff digit At
-- statement:
--   `LowDigits p n` iff every indexed base-`p` digit is `≤ (p-1)/2`.
--   Out-of-range indices give digit `0 ≤ (p-1)/2`, so the quantifier is over all `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L63-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean#L63-L76

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

theorem Egrs75.RepairPaperfaithful.lowDigits_iff_digitAt {p n : ℕ} (hp : 2 ≤ p) :
    LowDigits p n ↔ ∀ i, digitAt p i n ≤ (p - 1) / 2 := by sorry
