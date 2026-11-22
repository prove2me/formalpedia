-- Prove2me | Theorems.Thm_Egrs75_RepairDV_badCount_filter_append
-- name    : Egrs75.RepairDV.badCount_filter_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:05.610428+00:00
-- url     : https://prove2.me/theorems/bc482f5e-8cf7-496b-8086-097c6a47b036
-- title:
--   Repair DV: bad Count filter append
-- statement:
--   `badCountQ` additivity over `filter`/`append`: the bad count of a digit list
--   that splits as `L₁ ++ L₂` is the sum of the two bad counts.  Used to read the bad
--   count off a high/low decomposition of `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L63-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L63-L66

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

theorem Egrs75.RepairDV.badCount_filter_append (q : ℕ) (L₁ L₂ : List ℕ) :
    ((L₁ ++ L₂).filter (fun d => bigQ q d)).length =
      (L₁.filter (fun d => bigQ q d)).length + (L₂.filter (fun d => bigQ q d)).length := by sorry
