-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
-- name    : DeciSigma1.Holes.Fresh.marker_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:56.747171+00:00
-- url     : https://prove2.me/theorems/8cb17e5f-6f55-4d73-8bc0-0691bdb9e44d
-- title:
--   Fresh: marker zero
-- statement:
--   The Fresh construction uses the marker zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L427-L427
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L427-L427

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

theorem DeciSigma1.Holes.Fresh.marker_zero (l : Fin k) : marker W 0 l = [] := by sorry

attribute [defeq] DeciSigma1.Holes.Fresh.marker_zero
