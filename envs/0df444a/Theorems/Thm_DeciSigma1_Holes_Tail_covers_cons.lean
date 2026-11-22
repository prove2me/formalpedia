-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_covers_cons
-- name    : DeciSigma1.Holes.Tail.covers_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:17.513812+00:00
-- url     : https://prove2.me/theorems/c2a24081-c7b3-4388-affa-1c8ea3b31c04
-- title:
--   Tail: covers cons
-- statement:
--   The Tail construction uses the covers cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L399-L401
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L399-L401

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

theorem DeciSigma1.Holes.Tail.covers_cons {f : PeriodicFactor} {fs : List PeriodicFactor} {x : ℕ} :
    Covers (f :: fs) x ↔ (f.start ≤ x ∧ x < f.stop) ∨ Covers fs x := by sorry
