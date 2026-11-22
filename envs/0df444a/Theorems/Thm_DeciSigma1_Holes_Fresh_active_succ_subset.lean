-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset
-- name    : DeciSigma1.Holes.Fresh.active_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:05.006894+00:00
-- url     : https://prove2.me/theorems/cc1be102-4cd9-4b8f-b497-30650e39fe56
-- title:
--   Fresh: active succ subset
-- statement:
--   The Fresh construction uses the active succ subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L452-L455
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L452-L455

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α)

theorem DeciSigma1.Holes.Fresh.active_succ_subset (t : ℕ) : active W (t + 1) ⊆ active W t := by sorry
