-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_uncoveredTailPositions_le
-- name    : DeciSigma1.Holes.Tail.card_uncoveredTailPositions_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:10.21199+00:00
-- url     : https://prove2.me/theorems/30e3c237-4c92-42e4-8880-b9838eaaba33
-- title:
--   Tail: card uncovered Tail Positions le
-- statement:
--   Uncovered tail positions after the conversion: uncovered by the factors, or charged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L150-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L150-L163

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.card_uncoveredTailPositions_le (M : StructuralReader α S k) (U : Fin k → List α)
    {runs rs : Finset (RunSpec k)}
    (hsub : rs ⊆ runs) (i : Fin k) {fs : List PeriodicFactor} {X : Finset ℕ}
    (hX : ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X) :
    (uncoveredTailPositions M U runs i).card ≤
        (uncoveredPositions fs (M.firstRejection U i) (U i).length).card + X.card := by sorry
