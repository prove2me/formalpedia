-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_level_succ_succ
-- name    : DeciSigma1.Holes.Fresh.level_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:17.728799+00:00
-- url     : https://prove2.me/theorems/5c7928e1-f394-4dd8-b3ac-03fca6f990ad
-- title:
--   Fresh: level succ succ
-- statement:
--   The Fresh construction uses the level succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L431-L431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L431-L431

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

theorem DeciSigma1.Holes.Fresh.level_succ_succ (t : ℕ) : level W (t + 2) = (level W (t + 1)).next W := by sorry
