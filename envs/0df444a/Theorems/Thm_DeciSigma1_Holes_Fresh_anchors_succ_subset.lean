-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_succ_subset
-- name    : DeciSigma1.Holes.Fresh.anchors_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:27.321199+00:00
-- url     : https://prove2.me/theorems/c9530b6f-84c4-409c-8f13-f07087e21c70
-- title:
--   Fresh: anchors succ subset
-- statement:
--   The Fresh construction uses the anchors succ subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L604-L606
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L604-L606

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

theorem DeciSigma1.Holes.Fresh.anchors_succ_subset (t : ℕ) (l : Fin k) :
    anchors W (t + 1) l ⊆ anchors W t l := by sorry
