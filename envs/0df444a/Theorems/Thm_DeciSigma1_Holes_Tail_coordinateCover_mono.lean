-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_coordinateCover_mono
-- name    : DeciSigma1.Holes.Tail.coordinateCover_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:21.395587+00:00
-- url     : https://prove2.me/theorems/ce799834-d842-4ca1-8cff-523f9432e000
-- title:
--   Tail: coordinate Cover mono
-- statement:
--   A periodic cover at level `l` is one at every higher level.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L489-L492
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L489-L492

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
variable {σ N : ℕ}

theorem DeciSigma1.Holes.Tail.coordinateCover_mono (C : LevelBounds σ k N) {l l' : ℕ} (hl : l ≤ l')
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : CoordinateCover C l M W i) : CoordinateCover C l' M W i := by sorry
