-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_anti
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:31:23.670318+00:00
-- url     : https://prove2.me/theorems/386df100-0d0b-43dc-9512-217b2210f2f8
-- title:
--   Fresh: context Anchors anti
-- statement:
--   In every text, the anchors of a level are anchors of every lower level.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L125-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L125-L129

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_anti

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.contextAnchors_anti {r t : ℕ} (hrt : r ≤ t) (u : List α) :
    contextAnchors W t u ⊆ contextAnchors W r u := by sorry
