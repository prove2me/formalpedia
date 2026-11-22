-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_bounds
-- name    : DeciSigma1.Holes.Fresh.depthCut_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:50.012595+00:00
-- url     : https://prove2.me/theorems/287d7e99-bab7-49a3-88ba-57acdac936c9
-- title:
--   Fresh: depth Cut bounds
-- statement:
--   All depth cuts lie between the start and the end of the upper occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L142-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L142-L149

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

theorem DeciSigma1.Holes.Fresh.depthCut_bounds {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d ≤ lowerBlockCount W t o) :
    o.2.1 ≤ depthCut W t o d ∧ depthCut W t o d ≤ o.2.2 := by sorry
