-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_stable_level
-- name    : DeciSigma1.Holes.Tail.exists_stable_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:33.74965+00:00
-- url     : https://prove2.me/theorems/f10300c1-d05a-4d45-b64d-7d4b2e3abd70
-- title:
--   Tail: exists stable level
-- statement:
--   Some level `2 ≤ l ≤ levelCount k` has, for every coordinate, the same periodic cover
--   property at levels `l - 1` and `l`, and the same level cover property at levels `l - 2` and
--   `l - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L722-L748
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L722-L748

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S]

theorem DeciSigma1.Holes.Tail.exists_stable_level (C : LevelBounds σ k (Fintype.card S)) (M : StructuralReader α S k)
    (W : Fin k → List α) (hE : ∀ i, M.Eligible W i) :
    ∃ l, 2 ≤ l ∧ l ≤ levelCount k ∧
        ∀ i, (CoordinateCover C (l - 1) M W i ↔ CoordinateCover C l M W i) ∧
      (LevelCoverProperty C (l - 2) M W i ↔ LevelCoverProperty C (l - 1) M W i) := by sorry
