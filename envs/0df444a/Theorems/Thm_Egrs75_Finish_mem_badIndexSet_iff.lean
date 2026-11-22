-- Prove2me | Theorems.Thm_Egrs75_Finish_mem_badIndexSet_iff
-- name    : Egrs75.Finish.mem_badIndexSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:21.19504+00:00
-- url     : https://prove2.me/theorems/9d0d70c8-b160-4eec-ab49-92eb3395eb3d
-- title:
--   Finish: mem bad Index Set iff
-- statement:
--   `i ∈ badIndexSet q n ↔ BadAt q i n`, for all `i` (KERNEL-CLEAN).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L103-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L103-L119

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe

theorem Egrs75.Finish.mem_badIndexSet_iff {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by sorry
