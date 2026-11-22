-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_Ioc_marker_le
-- name    : DeciSigma1.Holes.Fresh.card_anchors_Ioc_marker_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:01.187988+00:00
-- url     : https://prove2.me/theorems/44fe5972-c8ba-4046-a257-aba9d51e1500
-- title:
--   Fresh: card anchors Ioc marker le
-- statement:
--   The same bound counting the right end: at most `k (N - 1) + 2` anchors of level `t` in the
--   half-open window `(a, a + |σ|]` of an occurrence of `σ` at `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L909-L929
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L909-L929

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

theorem DeciSigma1.Holes.Fresh.card_anchors_Ioc_marker_le {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p ≤ a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 2 := by sorry
