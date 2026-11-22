-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixNode_suffix
-- name    : DeciSigma1.Holes.Tail.suffixNode_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:46.799821+00:00
-- url     : https://prove2.me/theorems/82d067e0-d0b4-4edb-b992-d570d6d67018
-- title:
--   Tail: suffix Node suffix
-- statement:
--   A suffix `p ∈ D` of `w` is a suffix of the word of the suffix node of `w`, and the state before
--   it is read from the node.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L372-L391
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L372-L391

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

theorem DeciSigma1.Holes.Tail.suffixNode_suffix (T : Table α S k) (q0 : S) {w p : List α} (hp : p <:+ w)
    (hpD : p ∈ D) :
    p <:+ (suffixNode T q0 D w).1 ∧
      runFrom T.step q0 (w.take (w.length - p.length)) =
        runFrom T.step (suffixNode T q0 D w).2
          ((suffixNode T q0 D w).1.take ((suffixNode T q0 D w).1.length - p.length)) := by sorry
