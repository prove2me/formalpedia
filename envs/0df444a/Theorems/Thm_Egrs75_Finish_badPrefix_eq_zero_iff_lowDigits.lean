-- Prove2me | Theorems.Thm_Egrs75_Finish_badPrefix_eq_zero_iff_lowDigits
-- name    : Egrs75.Finish.badPrefix_eq_zero_iff_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:22.455219+00:00
-- url     : https://prove2.me/theorems/96678b29-1f7f-4653-97ae-c2a5fc97d41a
-- title:
--   Finish: bad Prefix eq zero iff low Digits
-- statement:
--   **Base case (KERNEL-CLEAN).**  `badPrefix q n = 0 ↔ LowDigits q n`.  The bitmask
--   vanishes iff there are no bad base-`q` digits, i.e. `badIndexSet` is empty, i.e.
--   `badCountQ q n = 0`, i.e. `LowDigits q n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L142-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L142-L162

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

theorem Egrs75.Finish.badPrefix_eq_zero_iff_lowDigits {q n : ℕ} (hq : 1 < q) :
    badPrefix q n = 0 ↔ LowDigits q n := by sorry
