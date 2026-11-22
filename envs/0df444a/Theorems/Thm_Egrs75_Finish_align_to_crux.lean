-- Prove2me | Theorems.Thm_Egrs75_Finish_align_to_crux
-- name    : Egrs75.Finish.align_to_crux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:29.727494+00:00
-- url     : https://prove2.me/theorems/a1545111-6abb-4864-8c0a-b90d963813b6
-- title:
--   Finish: align to crux
-- statement:
--   ALIGN ⟹ crux (KERNEL-CLEAN; = `CruxClose.align_imp_crux` / `FinalAsm.align_to_crux`,
--   inlined to avoid the hyphenated-module / `Equidist_fromscratch`-`sorry` import).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L419-L425
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L419-L425

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
public import Theorems.Thm_Egrs75_MuFinish_align_to_crux

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

theorem Egrs75.Finish.align_to_crux {p q : ℕ}
    (halign : ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by sorry
