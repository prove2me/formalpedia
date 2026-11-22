-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_with_run_cover
-- name    : DeciSigma1.Holes.Tail.exists_hole_with_run_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:17.257122+00:00
-- url     : https://prove2.me/theorems/93fa11cb-667c-41ae-a36b-c6bea6d20ba1
-- title:
--   Tail: exists hole with run cover
-- statement:
--   Every hole has a hole whose immortal rejected tails are covered by `pieceCountBase + 3`
--   designated runs per word, of period at most `D = periodBound (levelCount k)` and length at least
--   `2D`, up to `uncoveredLengthBound C` positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L220-L360
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L220-L360

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
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Tail.exists_hole_with_run_cover (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧
      HasScaledRunCover M W' (C.pieceCountBase + 3) (C.periodBound (levelCount k))
          (uncoveredLengthBound C) := by sorry
