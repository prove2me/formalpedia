-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
-- name    : DeciSigma1.Holes.Fresh.mem_active_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:54.493054+00:00
-- url     : https://prove2.me/theorems/bced939b-1686-4239-93ac-b10e1fb98a3f
-- title:
--   Fresh: mem active one
-- statement:
--   The coordinates active at level `1` are those with a nonempty word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L424-L425
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L424-L425

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

theorem DeciSigma1.Holes.Fresh.mem_active_one {l : Fin k} : l ∈ active W 1 ↔ W l ≠ [] := by sorry
