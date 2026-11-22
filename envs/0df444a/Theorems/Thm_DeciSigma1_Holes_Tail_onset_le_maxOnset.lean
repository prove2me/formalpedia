-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_onset_le_maxOnset
-- name    : DeciSigma1.Holes.Tail.onset_le_maxOnset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:06.254505+00:00
-- url     : https://prove2.me/theorems/95034b98-03e9-4e42-975e-bdf27b21499b
-- title:
--   Tail: onset le max Onset
-- statement:
--   The Tail construction uses the onset le max Onset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L991-L992
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L991-L992

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
omit [DecidableEq ι]

theorem DeciSigma1.Holes.Tail.onset_le_maxOnset (Ω : ι → Ray α) (i : ι) : (Ω i).onset ≤ maxOnset Ω := by sorry
