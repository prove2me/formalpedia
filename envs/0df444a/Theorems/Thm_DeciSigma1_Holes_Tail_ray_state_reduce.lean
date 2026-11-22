-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ray_state_reduce
-- name    : DeciSigma1.Holes.Tail.ray_state_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:59.954584+00:00
-- url     : https://prove2.me/theorems/1b90b149-a1f5-448d-88e5-6f93ff4ce8b7
-- title:
--   Tail: ray state reduce
-- statement:
--   Every cut of a ray has a cut at or before it and below the horizon with the same state and
--   the same infinite suffix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L854-L909
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L854-L909

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
variable (M : StructuralReader α S k)
variable {M}
variable [DecidableEq α] [Fintype S]

theorem DeciSigma1.Holes.Tail.ray_state_reduce (q : S) (Ω : Ray α) (a : ℕ) :
    ∃ a', a' ≤ a ∧ a' < rayHorizon S Ω ∧ rayState M q Ω a' = rayState M q Ω a ∧
      ∀ t, Ω.stream (a' + t) = Ω.stream (a + t) := by sorry
