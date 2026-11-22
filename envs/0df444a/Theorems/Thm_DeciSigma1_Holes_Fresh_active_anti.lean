-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_active_anti
-- name    : DeciSigma1.Holes.Fresh.active_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:50.299798+00:00
-- url     : https://prove2.me/theorems/665561d9-3443-4c8a-8d52-f94b43383b4c
-- title:
--   Fresh: active anti
-- statement:
--   The Fresh construction uses the active anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L457-L460
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L457-L460

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

theorem DeciSigma1.Holes.Fresh.active_anti {s t : ℕ} (h : s ≤ t) : active W t ⊆ active W s := by sorry
