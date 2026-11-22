-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_topLevel_spec
-- name    : DeciSigma1.Holes.Fresh.topLevel_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:11.067807+00:00
-- url     : https://prove2.me/theorems/194ccffd-fe94-44c9-9711-c11bc380abc0
-- title:
--   Fresh: top Level spec
-- statement:
--   `topLevel W` is the least `t` with no active coordinate at level `t + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L701-L709
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L701-L709

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
variable {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.topLevel_spec :
    active W (topLevel W + 1) = ∅ ∧ ∀ t < topLevel W, active W (t + 1) ≠ ∅ := by sorry
