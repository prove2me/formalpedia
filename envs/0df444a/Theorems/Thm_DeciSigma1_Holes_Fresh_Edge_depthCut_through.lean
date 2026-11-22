-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_depthCut_through
-- name    : DeciSigma1.Holes.Fresh.Edge.depthCut_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:19.875586+00:00
-- url     : https://prove2.me/theorems/11f743ae-9f76-4eb7-879c-cad1e9101732
-- title:
--   Edge: depth Cut through
-- statement:
--   For an occurrence that traverses the edge, the cut at depth `d ≤ endDepth` is its end minus a
--   length that depends only on the edge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L567-L571
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L567-L571

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)

theorem DeciSigma1.Holes.Fresh.Edge.depthCut_through {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (h : e.TraversedBy o) {d : ℕ} (hd : d ≤ e.endDepth) :
    depthCut W t o d + firstBlocksLength e.blocks.reverse d = o.2.2 := by sorry
