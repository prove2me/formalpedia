-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_level_anti
-- name    : DeciSigma1.Holes.Fresh.level_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:06.378796+00:00
-- url     : https://prove2.me/theorems/99afda5c-4906-499d-b657-6161b8bf7f65
-- title:
--   Fresh: level anti
-- statement:
--   Every level `t + 1` of the hierarchy of a tuple is a factor antichain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L496-L498
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L496-L498

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

theorem DeciSigma1.Holes.Fresh.level_anti : ∀ t, (level W (t + 1)).FactorAntichain
  := by sorry
