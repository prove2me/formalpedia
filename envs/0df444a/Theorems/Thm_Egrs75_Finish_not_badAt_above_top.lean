-- Prove2me | Theorems.Thm_Egrs75_Finish_not_badAt_above_top
-- name    : Egrs75.Finish.not_badAt_above_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:07.022989+00:00
-- url     : https://prove2.me/theorems/2d397b94-1dde-4e38-85fd-c431469641e0
-- title:
--   Finish: not bad At above top
-- statement:
--   Above the top bad index, nothing is `BadAt` (KERNEL-CLEAN, from `digit_good_above_top`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L122-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L122-L126

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

theorem Egrs75.Finish.not_badAt_above_top {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : topBadIndex q n < i) : ¬ BadAt q i n := by sorry
