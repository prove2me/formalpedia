-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_inside_marker_le
-- name    : DeciSigma1.Holes.Fresh.card_anchors_inside_marker_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:11.449939+00:00
-- url     : https://prove2.me/theorems/806739f1-5576-4e75-b0a6-57e451734f75
-- title:
--   Fresh: card anchors inside marker le
-- statement:
--   In a fresh tuple, an occurrence of a marker of level `t + 1` in any text has at most
--   `k (N - 1) + 1` anchors of level `t` strictly inside.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L849-L905
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L849-L905

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
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.card_anchors_inside_marker_le {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 1 := by sorry
