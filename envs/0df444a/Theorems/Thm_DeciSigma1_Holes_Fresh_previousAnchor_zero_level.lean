-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_zero_level
-- name    : DeciSigma1.Holes.Fresh.previousAnchor_zero_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:39.037424+00:00
-- url     : https://prove2.me/theorems/d42c2ba3-661c-46e1-a41c-f2ce69ee546d
-- title:
--   Fresh: previous Anchor zero level
-- statement:
--   At level `0` the lower blocks are single letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L890-L898
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L890-L898

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

theorem DeciSigma1.Holes.Fresh.previousAnchor_zero_level (l : Fin k) {q : ℕ}
    (hq : 1 ≤ q) (hql : q ≤ (W l).length) : previousAnchor (anchors W 0 l) q = q - 1 := by sorry
