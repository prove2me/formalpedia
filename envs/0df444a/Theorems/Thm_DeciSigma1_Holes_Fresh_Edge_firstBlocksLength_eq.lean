-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_firstBlocksLength_eq
-- name    : DeciSigma1.Holes.Fresh.Edge.firstBlocksLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:45.966178+00:00
-- url     : https://prove2.me/theorems/0e8f7a68-6f73-49e3-af89-10616d6c0a9d
-- title:
--   Edge: first Blocks Length eq
-- statement:
--   An occurrence that traverses the edge has the same last `endDepth` lower block lengths as the
--   parse of the edge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L555-L563
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L555-L563

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

theorem DeciSigma1.Holes.Fresh.Edge.firstBlocksLength_eq {o : Fin k × ℕ × ℕ} (h : e.TraversedBy o) {d : ℕ}
    (hd : d ≤ e.endDepth) :
    firstBlocksLength (reversedBlocks W t o) d = firstBlocksLength e.blocks.reverse d := by sorry
