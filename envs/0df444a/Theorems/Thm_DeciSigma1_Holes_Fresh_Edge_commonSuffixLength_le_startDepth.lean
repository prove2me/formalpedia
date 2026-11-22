-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_commonSuffixLength_le_startDepth
-- name    : DeciSigma1.Holes.Fresh.Edge.commonSuffixLength_le_startDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:39.13323+00:00
-- url     : https://prove2.me/theorems/9bce70b8-0160-43f7-9cde-41a77cfe8c10
-- title:
--   Edge: common Suffix Length le start Depth
-- statement:
--   A parse whose common suffix with the parse of the edge is shorter than `endDepth` has common
--   suffix at most `startDepth`: no trie node lies strictly inside an edge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L527-L531
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L527-L531

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

theorem DeciSigma1.Holes.Fresh.Edge.commonSuffixLength_le_startDepth {Y : List (List α)} (hY : Y ∈ upperParses W t)
    (h : commonSuffixLength e.blocks Y < e.endDepth) :
    commonSuffixLength e.blocks Y ≤ e.startDepth := by sorry
