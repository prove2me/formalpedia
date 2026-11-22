-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_of_le_longestPeriodicSuffixLength
-- name    : DeciSigma1.Holes.Tail.exists_of_le_longestPeriodicSuffixLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:16.121994+00:00
-- url     : https://prove2.me/theorems/dc067c4c-10e6-438c-b0d0-0bb42fb0f89e
-- title:
--   Tail: exists of le longest Periodic Suffix Length
-- statement:
--   The Tail construction uses the exists of le longest Periodic Suffix Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L456-L466
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L456-L466

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

theorem DeciSigma1.Holes.Tail.exists_of_le_longestPeriodicSuffixLength [DecidableEq α] {w : List α} {E Y : ℕ} (hY : 0 < Y)
    (h : Y ≤ longestPeriodicSuffixLength E w) : ∃ s p, 0 < p ∧ p ≤ E ∧ s ≤ w.length ∧
        PeriodicOn w p s w.length ∧
      Y ≤ w.length - s := by sorry
