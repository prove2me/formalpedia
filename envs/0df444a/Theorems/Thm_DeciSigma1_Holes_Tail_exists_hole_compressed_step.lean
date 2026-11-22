-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_compressed_step
-- name    : DeciSigma1.Holes.Tail.exists_hole_compressed_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:46.785782+00:00
-- url     : https://prove2.me/theorems/e6ff5579-6885-4399-91a4-6ff05648e270
-- title:
--   Tail: exists hole compressed step
-- statement:
--   One pass of compression: shorten the class of a designated run of largest period. The other
--   designated runs survive at their retained cuts, and the processed runs become uncovered
--   positions, at most `pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E)` each.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L368-L528
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L368-L528

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
variable [DecidableEq α] [Fintype S] [DecidableEq S]
open Classical

theorem DeciSigma1.Holes.Tail.exists_hole_compressed_step (M : StructuralReader α S k) {U : Fin k → List α}
    (hU : M.IsHole U) {n D E : ℕ}
    (runs : Finset (RunSpec k)) (hcard : runs.card ≤ n + 1) (hruns : ∀ r ∈ runs, IsBoundedRun U D r)
    (hE : ∑ i,
        (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) ≤ E)
    (hne : runs.Nonempty) :
    ∃ U', M.IsHole U' ∧
      HasBoundedRunCover M U' n D (E + (n + 1) * Periodic.pieceLengthBound (Fintype.card S) D
        (k * (Fintype.card S - 1)) (2 * (n + 1) + E)) := by sorry
