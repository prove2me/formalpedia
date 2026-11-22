-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_rejectedTailLength_le
-- name    : DeciSigma1.Holes.Tail.exists_hole_rejectedTailLength_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:58.5828+00:00
-- url     : https://prove2.me/theorems/f0c24107-06dc-4d43-b47c-4ce6e4122385
-- title:
--   Tail: exists hole rejected Tail Length le
-- statement:
--   The bound on rejected tails: a structural reader with `k` starts and `N` states over an
--   alphabet of size `σ` that has a hole has a hole whose immortal coordinates have rejected tails
--   of at most `tailLengthBound σ k N` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L611-L617
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L611-L617

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
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Tail.exists_hole_rejectedTailLength_le (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) →
      M.rejectedTailLength W' i ≤ tailLengthBound (Fintype.card α) k (Fintype.card S) := by sorry
