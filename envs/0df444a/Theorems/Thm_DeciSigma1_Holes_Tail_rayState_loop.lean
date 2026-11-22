-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_rayState_loop
-- name    : DeciSigma1.Holes.Tail.rayState_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:59.03647+00:00
-- url     : https://prove2.me/theorems/f92180ea-01e9-454c-b361-3ca08a9ec2b9
-- title:
--   Tail: ray State loop
-- statement:
--   A state loop along a stretch whose text repeats loops forever.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L831-L844
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L831-L844

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

theorem DeciSigma1.Holes.Tail.rayState_loop (q : S) (Ω : Ray α) {x d : ℕ}
    (hxd : rayState M q Ω (x + d) = rayState M q Ω x)
    (hshift : ∀ s, Ω.stream (x + d + s) = Ω.stream (x + s)) :
    ∀ m t, rayState M q Ω (x + t + m * d) = rayState M q Ω (x + t) := by sorry
