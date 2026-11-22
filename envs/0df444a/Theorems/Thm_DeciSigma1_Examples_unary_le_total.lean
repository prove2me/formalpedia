-- Prove2me | Theorems.Thm_DeciSigma1_Examples_unary_le_total
-- name    : DeciSigma1.Examples.unary_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:26.113855+00:00
-- url     : https://prove2.me/theorems/38c671b5-138b-4c23-b672-979cc423a673
-- title:
--   Examples: unary le total
-- statement:
--   Unary trees `⊥ < f(⊥) < f(f(⊥)) < … < f(f(…))` form a chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L54-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L54-L63

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints

theorem DeciSigma1.Examples.unary_le_total (t u : PrefixSet 1) : t ≤ u ∨ u ≤ t := by sorry
