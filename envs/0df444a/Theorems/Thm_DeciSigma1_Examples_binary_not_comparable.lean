-- Prove2me | Theorems.Thm_DeciSigma1_Examples_binary_not_comparable
-- name    : DeciSigma1.Examples.binary_not_comparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:32.969012+00:00
-- url     : https://prove2.me/theorems/690539b6-2e46-4b61-a80f-be4599fc550e
-- title:
--   Examples: binary not comparable
-- statement:
--   Over binary trees, `x ≤ y ∨ y ≤ x` is not entailed: `f(f(⊥, ⊥), ⊥)` and
--   `f(⊥, f(⊥, ⊥))` are incomparable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L88-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L88-L96

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

theorem DeciSigma1.Examples.binary_not_comparable :
    ¬ Entailment.DisjEntailsIn (fun _ => True) ([] : List (TopFree.Lit 2 (Fin 2))) swapQueries := by sorry
