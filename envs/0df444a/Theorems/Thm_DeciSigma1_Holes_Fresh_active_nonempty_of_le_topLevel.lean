-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_active_nonempty_of_le_topLevel
-- name    : DeciSigma1.Holes.Fresh.active_nonempty_of_le_topLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:48.025637+00:00
-- url     : https://prove2.me/theorems/3e81fe8b-5cf8-45c5-8e58-e953cc77536b
-- title:
--   Fresh: active nonempty of le top Level
-- statement:
--   The Fresh construction uses the active nonempty of le top Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L711-L714
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L711-L714

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

theorem DeciSigma1.Holes.Fresh.active_nonempty_of_le_topLevel {t : ℕ} (ht : 1 ≤ t) (h : t ≤ topLevel W) :
    (active W t).Nonempty := by sorry
