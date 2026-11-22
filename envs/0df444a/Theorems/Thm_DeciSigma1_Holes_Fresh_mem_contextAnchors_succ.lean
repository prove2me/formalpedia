-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
-- name    : DeciSigma1.Holes.Fresh.mem_contextAnchors_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:51.846397+00:00
-- url     : https://prove2.me/theorems/2b76e9f9-23bf-4ef8-b5bc-67aa62b88054
-- title:
--   Fresh: mem context Anchors succ
-- statement:
--   The Fresh construction uses the mem context Anchors succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L437-L440
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L437-L440

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

theorem DeciSigma1.Holes.Fresh.mem_contextAnchors_succ {t : ℕ} {u : List α} {e : ℕ} :
    e ∈ contextAnchors W (t + 1) u ↔
      e ≤ u.length ∧ ∃ m ∈ active W (t + 1), marker W (t + 1) m <:+ u.take e := by sorry
