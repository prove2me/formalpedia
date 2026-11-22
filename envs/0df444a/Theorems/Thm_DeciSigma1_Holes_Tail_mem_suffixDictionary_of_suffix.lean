-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_mem_suffixDictionary_of_suffix
-- name    : DeciSigma1.Holes.Tail.mem_suffixDictionary_of_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:23.282286+00:00
-- url     : https://prove2.me/theorems/5d5bc883-d3b6-42d3-915d-4740c0c8d2b4
-- title:
--   Tail: mem suffix Dictionary of suffix
-- statement:
--   The suffixes of length at most `B` of a target lie in the suffix dictionary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L244-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L244-L250

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
variable [DecidableEq α]
variable {ts : List (List α)} {B : ℕ}

theorem DeciSigma1.Holes.Tail.mem_suffixDictionary_of_suffix {t p : List α} (ht : t ∈ ts) (hp : p <:+ t)
    (hpB : p.length ≤ B) : p ∈ suffixDictionary ts B := by sorry
