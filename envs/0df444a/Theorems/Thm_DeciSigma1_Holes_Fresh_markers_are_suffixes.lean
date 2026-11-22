-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_markers_are_suffixes
-- name    : DeciSigma1.Holes.Fresh.markers_are_suffixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:23.837082+00:00
-- url     : https://prove2.me/theorems/94731b09-127b-4a7b-a479-a11cd4dbbf8f
-- title:
--   Fresh: markers are suffixes
-- statement:
--   The Fresh construction uses the markers are suffixes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L449-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L449-L450

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

theorem DeciSigma1.Holes.Fresh.markers_are_suffixes (t : ℕ) :
    (level W t).MarkersAreSuffixes W := by sorry
