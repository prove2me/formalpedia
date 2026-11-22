-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_endDepth_le_length
-- name    : DeciSigma1.Holes.Fresh.Edge.endDepth_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:40.241812+00:00
-- url     : https://prove2.me/theorems/ec825884-04ff-4901-b347-8658200e5b17
-- title:
--   Edge: end Depth le length
-- statement:
--   The Edge construction uses the end Depth le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L522-L523
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L522-L523

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

theorem DeciSigma1.Holes.Fresh.Edge.endDepth_le_length :
    e.endDepth ≤ e.blocks.length := by sorry
