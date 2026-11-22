-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_append_right
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:44.487541+00:00
-- url     : https://prove2.me/theorems/201645a7-08f3-42b7-985c-d4f59274cbbb
-- title:
--   Fresh: context Anchors append right
-- statement:
--   Anchors of a text are anchors of every extension of it to the left, shifted.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L676-L683
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L676-L683

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_append_right {t : ℕ} {u v : List α} {e : ℕ} (h : e ∈ contextAnchors W t v) :
    u.length + e ∈ contextAnchors W t (u ++ v) := by sorry
