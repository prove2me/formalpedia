-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_reduce_of_snoc
-- name    : DeciSigma1.Holes.Tail.pumpFactor_reduce_of_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:10.688937+00:00
-- url     : https://prove2.me/theorems/2dfa405d-03a7-490c-9805-8bf5575e1e2f
-- title:
--   Tail: pump Factor reduce of snoc
-- statement:
--   Under the hypotheses of `pumpFactor_period_of_snoc`, the value of `F` on every prefix of the
--   pumped factor is its value on a prefix of `x` of length at most `c'`, and longer than `c` if the
--   prefix of the pumped factor is.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L630-L645
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L630-L645

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

theorem DeciSigma1.Holes.Tail.pumpFactor_reduce_of_snoc {β : Type*} (F : List α → β) (G : β → α → β)
    (hF : ∀ w a, F (w ++ [a]) = G (F w) a) (hcc : c < c') (hc' : c' ≤ x.length)
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) :
    ∀ p ≤ c + L, ∃ p' ≤ c', (c < p → c < p') ∧
      F ((pumpFactor x c c' L).take p) = F (x.take p') := by sorry
