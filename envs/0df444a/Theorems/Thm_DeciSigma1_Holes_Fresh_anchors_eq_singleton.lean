-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_singleton
-- name    : DeciSigma1.Holes.Fresh.anchors_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:57.949393+00:00
-- url     : https://prove2.me/theorems/cc6903ed-3f52-4f21-b1cf-c7c246ddc5ce
-- title:
--   Fresh: anchors eq singleton
-- statement:
--   A coordinate that is not active at level `t + 1` is a single level-`t` block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L609-L637
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L609-L637

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

theorem DeciSigma1.Holes.Fresh.anchors_eq_singleton {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∉ active W (t + 1)) : anchors W t l = {(W l).length} := by sorry
