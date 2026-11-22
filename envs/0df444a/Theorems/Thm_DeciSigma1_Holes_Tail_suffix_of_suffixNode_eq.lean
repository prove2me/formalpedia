-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffix_of_suffixNode_eq
-- name    : DeciSigma1.Holes.Tail.suffix_of_suffixNode_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:46.553368+00:00
-- url     : https://prove2.me/theorems/9e1e34b0-b5b7-4f93-874d-a362dfbed15c
-- title:
--   Tail: suffix of suffix Node eq
-- statement:
--   Two words with the same suffix node have the same suffixes in `D`, with the same states before
--   them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L395-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L395-L402

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

theorem DeciSigma1.Holes.Tail.suffix_of_suffixNode_eq (T : Table α S k) (q0 : S) {w w' p : List α}
    (he : suffixNode T q0 D w = suffixNode T q0 D w') (hp : p <:+ w) (hpD : p ∈ D) :
    p <:+ w' ∧ runFrom T.step q0 (w'.take (w'.length - p.length)) =
      runFrom T.step q0 (w.take (w.length - p.length)) := by sorry
