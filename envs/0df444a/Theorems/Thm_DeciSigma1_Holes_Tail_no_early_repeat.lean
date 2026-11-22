-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_no_early_repeat
-- name    : DeciSigma1.Holes.Tail.no_early_repeat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:12.810867+00:00
-- url     : https://prove2.me/theorems/a7cc8df2-aa8f-4fb9-8f36-36c606babf56
-- title:
--   Tail: no early repeat
-- statement:
--   A state repeated at cuts `a' < a ≤ J` and followed by the same text up to the first rejected
--   cut `J` would give an earlier rejected cut, which is impossible.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L504-L522
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L504-L522

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
variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}

theorem DeciSigma1.Holes.Tail.no_early_repeat (h : M.Eligible W i) {a' a : ℕ} (ha : a' < a)
    (haJ : a ≤ M.firstRejection W i)
    (htext : ∀ t, t < M.firstRejection W i - a → (W i)[a' + t]? = (W i)[a + t]?)
    (hq : M.runPrefix W i a' = M.runPrefix W i a) : False := by sorry
