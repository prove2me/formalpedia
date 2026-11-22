-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixNode_append
-- name    : DeciSigma1.Holes.Tail.suffixNode_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:13.477148+00:00
-- url     : https://prove2.me/theorems/96434555-f014-4f33-a55e-014ef13a0c94
-- title:
--   Tail: suffix Node append
-- statement:
--   For a dictionary of words of length at most `|v|`, the suffix node of `u ++ v` depends only on
--   the state after `u` and on `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L420-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L420-L435

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

theorem DeciSigma1.Holes.Tail.suffixNode_append (T : Table α S k) (q0 : S) (hD : [] ∈ D) {u v : List α}
    (hB : ∀ r ∈ D, r.length ≤ v.length) :
    suffixNode T q0 D (u ++ v) = (dictSuffix D v, runFrom T.step (runFrom T.step q0 u)
      (v.take (v.length - (dictSuffix D v).length))) := by sorry
