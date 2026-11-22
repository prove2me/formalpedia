-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_above_top
-- name    : DeciSigma1.Holes.Fresh.anchors_above_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:28.031792+00:00
-- url     : https://prove2.me/theorems/6033418f-cf9f-460f-8b69-f9ba992b665a
-- title:
--   Fresh: anchors above top
-- statement:
--   Above the top level the only upper blocks are whole words.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L798-L806
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L798-L806

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.anchors_above_top (l : Fin k) :
    anchors W (topLevel W + 1) l = {(W l).length} := by sorry
