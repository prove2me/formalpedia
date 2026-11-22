-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_hasBoundedRunCover_of_covers
-- name    : DeciSigma1.Holes.Tail.hasBoundedRunCover_of_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:13.066271+00:00
-- url     : https://prove2.me/theorems/808edbcd-ceb8-4cb1-b917-df3abf577868
-- title:
--   Tail: has Bounded Run Cover of covers
-- statement:
--   A cover of every immortal tail by `≤ P` factors of period `≤ D` and `≤ T` letters gives
--   `HasBoundedRunCover` with `k·P` runs and `k (T + P·2D)` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L167-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L167-L202

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

theorem DeciSigma1.Holes.Tail.hasBoundedRunCover_of_covers
    (M : StructuralReader α S k)
    (U : Fin k → List α) {P D T : ℕ}
    (h : ∀ i, M.Immortal (M.endState U i) → PeriodicCover (U i) (M.firstRejection U i) P D T) :
    HasBoundedRunCover M U (k * P) D (k * (T + P * (2 * D))) := by sorry
