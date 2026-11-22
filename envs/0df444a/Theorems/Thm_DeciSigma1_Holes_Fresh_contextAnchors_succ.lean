-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_succ
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:25.585086+00:00
-- url     : https://prove2.me/theorems/8c94edea-f491-4051-92c2-ec5fd0674eb7
-- title:
--   Fresh: context Anchors succ
-- statement:
--   The Fresh construction uses the context Anchors succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L433-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L433-L435

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_succ (t : ℕ) (u : List α) :
    contextAnchors W (t + 1) u = (level W (t + 1)).markerEndCuts u := by sorry
