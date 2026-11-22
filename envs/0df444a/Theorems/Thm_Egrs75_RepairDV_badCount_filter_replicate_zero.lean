-- Prove2me | Theorems.Thm_Egrs75_RepairDV_badCount_filter_replicate_zero
-- name    : Egrs75.RepairDV.badCount_filter_replicate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:07.867098+00:00
-- url     : https://prove2.me/theorems/8e020909-dd27-4ce3-a94b-576933613209
-- title:
--   Repair DV: bad Count filter replicate zero
-- statement:
--   Appending zeros to a digit list does not change its bad count (since `0` is
--   never oversized for `q ≥ 1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L70-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L70-L72

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

theorem Egrs75.RepairDV.badCount_filter_replicate_zero (q k : ℕ) :
    ((List.replicate k 0).filter (fun d => bigQ q d)).length = 0 := by sorry
