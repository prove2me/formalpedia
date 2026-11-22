-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
-- name    : DeciSigma1.Holes.Fresh.marker_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:45.548392+00:00
-- url     : https://prove2.me/theorems/c997f2b9-d294-48e1-a7ed-824c47c738a4
-- title:
--   Fresh: marker suffix
-- statement:
--   Every marker is a suffix of its own word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L443-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L443-L447

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

theorem DeciSigma1.Holes.Fresh.marker_suffix (t : ℕ) (l : Fin k) : marker W t l <:+ W l := by sorry
