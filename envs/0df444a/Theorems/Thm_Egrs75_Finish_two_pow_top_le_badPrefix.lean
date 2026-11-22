-- Prove2me | Theorems.Thm_Egrs75_Finish_two_pow_top_le_badPrefix
-- name    : Egrs75.Finish.two_pow_top_le_badPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:18.742813+00:00
-- url     : https://prove2.me/theorems/3ca0c1b1-254c-4533-b9ea-0aaad52213d1
-- title:
--   Finish: two pow top le bad Prefix
-- statement:
--   **Lower bound (KERNEL-CLEAN).**  `2 ^ (topBadIndex q n) ≤ badPrefix q n`: the
--   top bad bit is one of the summands.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L171-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L171-L175

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

theorem Egrs75.Finish.two_pow_top_le_badPrefix {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    2 ^ (topBadIndex q n) ≤ badPrefix q n := by sorry
