-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
-- name    : DeciSigma1.Holes.Fresh.Edge.through_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:07.353728+00:00
-- url     : https://prove2.me/theorems/cd0305e8-6edc-4629-8bcc-636bc57f175b
-- title:
--   Edge: through iff
-- statement:
--   The Edge construction uses the through iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L533-L542
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L533-L542

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

theorem DeciSigma1.Holes.Fresh.Edge.through_iff {o : Fin k × ℕ × ℕ} :
    e.TraversedBy o ↔ e.endDepth ≤ lowerBlockCount W t o ∧ (reversedBlocks W t o).take e.endDepth =
        e.blocks.reverse.take e.endDepth := by sorry
