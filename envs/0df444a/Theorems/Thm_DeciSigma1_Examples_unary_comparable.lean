-- Prove2me | Theorems.Thm_DeciSigma1_Examples_unary_comparable
-- name    : DeciSigma1.Examples.unary_comparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:14.168833+00:00
-- url     : https://prove2.me/theorems/337c0302-2206-4261-a796-5dbe11bfbf7b
-- title:
--   Examples: unary comparable
-- statement:
--   Over unary trees, the empty constraint entails `x ≤ y ∨ y ≤ x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L69-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L69-L74

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

theorem DeciSigma1.Examples.unary_comparable :
    Entailment.DisjEntailsIn (fun _ => True) ([] : List (TopFree.Lit 1 (Fin 2))) swapQueries := by sorry
