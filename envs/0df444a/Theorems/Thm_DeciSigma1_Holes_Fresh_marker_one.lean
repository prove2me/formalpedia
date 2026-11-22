-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_one
-- name    : DeciSigma1.Holes.Fresh.marker_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:16.350234+00:00
-- url     : https://prove2.me/theorems/6d9dc7e0-d85f-48e9-b5ae-d70b3802a932
-- title:
--   Fresh: marker one
-- statement:
--   The Fresh construction uses the marker one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L429-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L429-L429

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

theorem DeciSigma1.Holes.Fresh.marker_one (l : Fin k) : marker W 1 l = (W l).drop ((W l).length - 1) := by sorry
