-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_of_append_right
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_of_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:46.802967+00:00
-- url     : https://prove2.me/theorems/556fa93e-74af-4893-9b8e-de90a2c4b9b5
-- title:
--   Fresh: context Anchors of append right
-- statement:
--   An anchor of `u ++ v` beyond `|u|` whose marker lies inside `v` is an anchor of `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L686-L692
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L686-L692

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

theorem DeciSigma1.Holes.Fresh.contextAnchors_of_append_right {t : ℕ} (ht : 1 ≤ t) {u v : List α} {e : ℕ} {m : Fin k}
    (hm : m ∈ active W t) (hs : marker W t m <:+ (u ++ v).take (u.length + e))
    (he : e ≤ v.length) (hin : (marker W t m).length ≤ e) : e ∈ contextAnchors W t v := by sorry
