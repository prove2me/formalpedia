-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_isWalk_append_singleton
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.isWalk_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:48.226278+00:00
-- url     : https://prove2.me/theorems/ef151697-1499-450b-aec7-b71c6f9dbbb6
-- title:
--   Difference System: is Walk append singleton
-- statement:
--   The Difference System construction uses the is Walk append singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L163-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L163-L171

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}

theorem DeciSigma1.Arithmetic.DifferenceSystem.isWalk_append_singleton {p : List ι} {i j : ι} (hp : D.IsWalk p)
    (hl : p.getLast? = some i) (hij : (D.edgeWeight i j).isSome) : D.IsWalk (p ++ [j]) := by sorry
