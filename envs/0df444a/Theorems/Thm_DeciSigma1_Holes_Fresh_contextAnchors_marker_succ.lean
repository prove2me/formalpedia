-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_marker_succ
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_marker_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:47.18915+00:00
-- url     : https://prove2.me/theorems/847653fb-2311-4de4-827e-8241fcd78c3d
-- title:
--   Fresh: context Anchors marker succ
-- statement:
--   Read as a text, a marker of level `t + 1` has exactly two anchors of level `t`: the end of
--   the level-`t` marker it starts with, and its own end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L554-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L554-L560

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_marker_succ {t : ℕ} (ht : 1 ≤ t) {l : Fin k} (hl : l ∈ active W (t + 1)) :
    ∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l ∧
      (marker W t m).length < (marker W (t + 1) l).length ∧
      contextAnchors W t (marker W (t + 1) l) =
        {(marker W t m).length, (marker W (t + 1) l).length} := by sorry
