-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_succ_subset
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:53.49784+00:00
-- url     : https://prove2.me/theorems/c748180d-3be1-4eac-bfe3-8c06cdaa0095
-- title:
--   Fresh: context Anchors succ subset
-- statement:
--   Anchors of level `t + 1` are anchors of level `t`, in every context.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L589-L602
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L589-L602

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_succ_subset (t : ℕ) (u : List α) :
    contextAnchors W (t + 1) u ⊆ contextAnchors W t u := by sorry
