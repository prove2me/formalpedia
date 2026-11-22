-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_exists_through
-- name    : DeciSigma1.Holes.Fresh.Edge.exists_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:44.04856+00:00
-- url     : https://prove2.me/theorems/1a0b564d-6d64-4b6d-be3a-4ce325ae4613
-- title:
--   Edge: exists through
-- statement:
--   Some upper occurrence has the parse of the edge, and it traverses the edge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L545-L551
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L545-L551

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

theorem DeciSigma1.Holes.Fresh.Edge.exists_through :
    ∃ o ∈ upperOccurrences W t, upperParse W t o = e.blocks ∧ e.TraversedBy o := by sorry
