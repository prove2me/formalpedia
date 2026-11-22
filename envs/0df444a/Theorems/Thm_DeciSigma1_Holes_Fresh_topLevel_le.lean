-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_topLevel_le
-- name    : DeciSigma1.Holes.Fresh.topLevel_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:07.921171+00:00
-- url     : https://prove2.me/theorems/16ce2e45-46c4-48eb-852e-72ac8dd5a27c
-- title:
--   Fresh: top Level le
-- statement:
--   The hierarchy of a fresh tuple has at most `k (N - 1)` levels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L838-L843
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L838-L843

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

theorem DeciSigma1.Holes.Fresh.topLevel_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i) :
    topLevel W ≤ k * (Fintype.card S - 1) := by sorry
