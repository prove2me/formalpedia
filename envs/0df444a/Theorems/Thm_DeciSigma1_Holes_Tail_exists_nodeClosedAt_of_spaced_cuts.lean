-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_nodeClosedAt_of_spaced_cuts
-- name    : DeciSigma1.Holes.Tail.exists_nodeClosedAt_of_spaced_cuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:18.232794+00:00
-- url     : https://prove2.me/theorems/0adab82f-f46d-479e-adaa-f8ad7b520562
-- title:
--   Tail: exists node Closed At of spaced cuts
-- statement:
--   Among the cuts `u, u + s, …, u + V s` of `x`, where `V = |D| · N` and `[] ∈ D`, two have the
--   same suffix node; they bound a closed factor of length at least `s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L470-L493
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L470-L493

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
variable [DecidableEq α] {D : Finset (List α)}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

theorem DeciSigma1.Holes.Tail.exists_nodeClosedAt_of_spaced_cuts [Fintype S] (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (x : List α) {s u : ℕ} (hs : 0 < s) (hu : u + s * (D.card * Fintype.card S) ≤ x.length) :
    ∃ c c', u ≤ c ∧ c' ≤ u + s * (D.card * Fintype.card S) ∧ s ≤ c' - c ∧
      NodeClosedAt T q0 D x c c' := by sorry
