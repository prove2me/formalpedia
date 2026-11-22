-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_edgePrefix_length
-- name    : DeciSigma1.Holes.Fresh.Edge.edgePrefix_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:46.215097+00:00
-- url     : https://prove2.me/theorems/07b39d44-2829-4ebe-8b3e-4e958d6e0ccc
-- title:
--   Edge: edge Prefix length
-- statement:
--   `edgePrefix e p` is as long as the text between the cuts at depths `endDepth` and `p` of every
--   traversing occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L205-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L205-L215

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

theorem DeciSigma1.Holes.Fresh.Edge.edgePrefix_length {t : ℕ} (e : Edge W t)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o)
    {p : ℕ} (hp : p ≤ e.endDepth) :
    (edgePrefix e p).length = depthCut W t o p - depthCut W t o e.endDepth := by sorry
