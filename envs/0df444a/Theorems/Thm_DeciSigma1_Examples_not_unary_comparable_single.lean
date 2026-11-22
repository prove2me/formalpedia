-- Prove2me | Theorems.Thm_DeciSigma1_Examples_not_unary_comparable_single
-- name    : DeciSigma1.Examples.not_unary_comparable_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:18.930153+00:00
-- url     : https://prove2.me/theorems/5a39eca2-5f87-4420-8354-d933a1bb790b
-- title:
--   Examples: not unary comparable single
-- statement:
--   Neither disjunct of `unary_comparable` is entailed on its own.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L77-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L77-L84

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

theorem DeciSigma1.Examples.not_unary_comparable_single (i : Fin 2) :
    ¬ Entailment.DisjEntailsIn (fun _ => True)
        ([] : List (TopFree.Lit 1 (Fin 2))) ![swapQueries i] := by sorry
