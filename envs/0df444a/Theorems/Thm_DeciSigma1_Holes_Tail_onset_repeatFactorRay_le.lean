-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_onset_repeatFactorRay_le
-- name    : DeciSigma1.Holes.Tail.onset_repeatFactorRay_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:11.143316+00:00
-- url     : https://prove2.me/theorems/87381d82-a4ce-4a11-afda-1472f2471281
-- title:
--   Tail: onset repeat Factor Ray le
-- statement:
--   The onset of the ray of a factor `x[c, c')` is at most `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L928-L930
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L928-L930

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

theorem DeciSigma1.Holes.Tail.onset_repeatFactorRay_le [DecidableEq α] {x : List α} {c c' : ℕ} (hcc : c < c')
    (hc' : c' ≤ x.length) : (repeatFactorRay x c c' hcc hc').onset ≤ c := by sorry
