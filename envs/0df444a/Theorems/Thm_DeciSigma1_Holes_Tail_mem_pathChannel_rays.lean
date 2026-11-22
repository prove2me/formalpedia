-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_mem_pathChannel_rays
-- name    : DeciSigma1.Holes.Tail.mem_pathChannel_rays
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:15.297829+00:00
-- url     : https://prove2.me/theorems/fe1ea99c-b4a6-4438-a82d-6a7e30fd5b52
-- title:
--   Tail: mem path Channel rays
-- statement:
--   A comparison among ray prefixes, read as cuts and states of the rays.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L1000-L1015
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L1000-L1015

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
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}
omit [Fintype S] [Fintype ι] [DecidableEq ι]

theorem DeciSigma1.Holes.Tail.mem_pathChannel_rays [DecidableEq S] {st : ι → S} {Ω : ι → Ray α} {L : ι → ℕ} {i j : ι}
    {pq : S × S} :
    pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
        (streamPrefix (Ω j).stream (L j)) ↔
      ∃ a ≤ L i, ∃ b ≤ L j, L j - b ≤ L i - a ∧
        (∀ t < L j - b, (Ω j).stream (b + t) = (Ω i).stream (a + t)) ∧
        pq = (rayState M (st i) (Ω i) a, rayState M (st j) (Ω j) b) := by sorry
