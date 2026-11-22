-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_tail_le_of_empty
-- name    : DeciSigma1.Holes.Tail.tail_le_of_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:38.353551+00:00
-- url     : https://prove2.me/theorems/079e5b25-a531-44d3-8fe5-c15c2e4297b1
-- title:
--   Tail: tail le of empty
-- statement:
--   The tail bound when no designated run is left: every immortal tail is uncovered.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L534-L543
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L534-L543

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
open Classical

theorem DeciSigma1.Holes.Tail.tail_le_of_empty (M : StructuralReader α S k) {U : Fin k → List α} {E : ℕ}
    (hE : ∑ i,
        (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U ∅ i).card else 0) ≤ E)
    (i : Fin k) (hi : M.Immortal (M.endState U i)) : M.rejectedTailLength U i ≤ E := by sorry
