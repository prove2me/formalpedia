-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_topBad_lt_of_good_from
-- name    : Egrs75.MoveDigits.topBad_lt_of_good_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:46.823547+00:00
-- url     : https://prove2.me/theorems/40054ec9-71e7-4fd6-a86d-5963602a2fc2
-- title:
--   Move Digits: top Bad lt of good from
-- statement:
--   If every digit at index `≥ x` is good, the top bad index is `< x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L155-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L155-L164

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.MoveDigits.topBad_lt_of_good_from {q n x : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hgood : ∀ idx, x ≤ idx → n / q ^ idx % q ≤ (q - 1) / 2) :
    topBadIndex q n < x := by sorry
