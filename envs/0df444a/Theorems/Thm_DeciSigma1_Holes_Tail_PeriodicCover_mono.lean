-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
-- name    : DeciSigma1.Holes.Tail.PeriodicCover.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:07.902889+00:00
-- url     : https://prove2.me/theorems/f459ea5b-2e12-4734-9511-249098bd3fb8
-- title:
--   Periodic Cover: mono
-- statement:
--   The Periodic Cover construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L392-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L392-L397

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.PeriodicCover.mono {w : List α} {J P E T P' E' T' : ℕ} (h : PeriodicCover w J P E T)
    (hP : P ≤ P')
    (hE : E ≤ E') (hT : T ≤ T') : PeriodicCover w J P' E' T' := by sorry
