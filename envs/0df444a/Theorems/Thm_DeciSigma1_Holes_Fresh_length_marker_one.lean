-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
-- name    : DeciSigma1.Holes.Fresh.length_marker_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:24.888359+00:00
-- url     : https://prove2.me/theorems/b142f6c1-1ffb-4c9c-bff8-bd8d99c99019
-- title:
--   Fresh: length marker one
-- statement:
--   The marker of a nonempty word at level `1` is a single letter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L484-L486
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L484-L486

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

theorem DeciSigma1.Holes.Fresh.length_marker_one {l : Fin k} (hl : l ∈ active W 1) : (marker W 1 l).length = 1 := by sorry
