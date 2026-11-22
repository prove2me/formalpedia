-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_sat_raySys_iff
-- name    : DeciSigma1.Holes.Tail.sat_raySys_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:05.70028+00:00
-- url     : https://prove2.me/theorems/d6e2a93c-5035-49e3-8cb8-9dca17ddac37
-- title:
--   Tail: sat ray Sys iff
-- statement:
--   The Tail construction uses the sat ray Sys iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L966-L988
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L966-L988

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}

theorem DeciSigma1.Holes.Tail.sat_raySys_iff {st : ι → S} {Ω : ι → Ray α} {J : ι → ℕ} {x : ι → ℤ} :
    (raySystem M st Ω J).Sat x ↔ ∀ i j, i ≠ j → ∀ a < rayHorizon S (Ω i), ∀ b ≤ J j,
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → x i + ((b : ℤ) - a + 1) ≤ x j := by sorry
