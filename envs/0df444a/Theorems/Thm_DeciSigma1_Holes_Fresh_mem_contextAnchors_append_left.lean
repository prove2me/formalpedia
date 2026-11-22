-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_append_left
-- name    : DeciSigma1.Holes.Fresh.mem_contextAnchors_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:03.714151+00:00
-- url     : https://prove2.me/theorems/39784594-125a-4ba2-91e6-2939cf6c1c71
-- title:
--   Fresh: mem context Anchors append left
-- statement:
--   Anchors at cuts inside a prefix are anchors of that prefix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L666-L673
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L666-L673

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

theorem DeciSigma1.Holes.Fresh.mem_contextAnchors_append_left {t : ℕ} {u v : List α} {e : ℕ} (he : e ≤ u.length) :
    e ∈ contextAnchors W t (u ++ v) ↔ e ∈ contextAnchors W t u := by sorry
