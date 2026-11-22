-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_rayState_add
-- name    : DeciSigma1.Holes.Tail.rayState_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:50.533804+00:00
-- url     : https://prove2.me/theorems/3ee07211-d285-420e-8837-b0c1a70bed69
-- title:
--   Tail: ray State add
-- statement:
--   The Tail construction uses the ray State add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L824-L828
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L824-L828

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
variable (M : StructuralReader α S k)
variable {M}

theorem DeciSigma1.Holes.Tail.rayState_add (q : S) (Ω : Ray α) (x t : ℕ) :
    rayState M q Ω (x + t) =
        runFrom M.step (rayState M q Ω x) (streamPrefix (fun i => Ω.stream (x + i)) t) := by sorry
