-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_full_iff
-- name    : DeciSigma1.Holes.Tail.periodicOn_full_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:07.935903+00:00
-- url     : https://prove2.me/theorems/36fd8f56-81c9-43fd-aee6-725a58c06eb6
-- title:
--   Tail: periodic On full iff
-- statement:
--   The Tail construction uses the periodic On full iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L432-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L432-L434

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

theorem DeciSigma1.Holes.Tail.periodicOn_full_iff {w : List α} {p s : ℕ} (hs : s ≤ w.length) :
    PeriodicOn w p s w.length ↔ (w.drop s).HasPeriod p := by sorry
