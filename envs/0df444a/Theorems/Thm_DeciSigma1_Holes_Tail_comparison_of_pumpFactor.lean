-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_comparison_of_pumpFactor
-- name    : DeciSigma1.Holes.Tail.comparison_of_pumpFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:44.881537+00:00
-- url     : https://prove2.me/theorems/d1b0a349-4c66-4cb3-b74f-2678f19c00e5
-- title:
--   Tail: comparison of pump Factor
-- statement:
--   If `x[c, c')` is closed for the suffix dictionary of the targets `ts` at window `B`, and no
--   occurrence of the suffix of length `B` of the target `t ∈ ts` ends in `(c, c']`, every comparison
--   of the pumped factor with `t`, read from any state `qt`, is a comparison of `x` with `t`. Empty
--   targets are included.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L655-L710
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L655-L710

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

theorem DeciSigma1.Holes.Tail.comparison_of_pumpFactor [DecidableEq α] [DecidableEq S] {T : Table α S k} {q0 qt : S}
    {x t : List α} {ts : List (List α)} {B c c' L : ℕ}
    (hcl : NodeClosedAt T q0 (suffixDictionary ts B) x c c') (ht : t ∈ ts)
    (hfree : NoSuffixOccurrenceEndsBetween x t B c c') (hL : c' - c ≤ L) :
    T.pathChannel q0 (pumpFactor x c c' L) qt t ⊆ T.pathChannel q0 x qt t := by sorry
