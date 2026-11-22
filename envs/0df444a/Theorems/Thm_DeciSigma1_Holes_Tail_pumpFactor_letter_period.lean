-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_letter_period
-- name    : DeciSigma1.Holes.Tail.pumpFactor_letter_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:40.344489+00:00
-- url     : https://prove2.me/theorems/28eaf7b9-8ae0-4de3-962b-896ec5fac36d
-- title:
--   Tail: pump Factor letter period
-- statement:
--   The letters of the pumped factor repeat with period `c' - c` from `c - B` on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L594-L604
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L594-L604

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}

theorem DeciSigma1.Holes.Tail.pumpFactor_letter_period (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p]? = (pumpFactor x c c' L)[p + (c' - c)]? := by sorry
