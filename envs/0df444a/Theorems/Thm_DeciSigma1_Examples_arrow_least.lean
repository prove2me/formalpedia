-- Prove2me | Theorems.Thm_DeciSigma1_Examples_arrow_least
-- name    : DeciSigma1.Examples.arrow_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:14.662967+00:00
-- url     : https://prove2.me/theorems/ebbf88bd-21ec-43e3-9d16-2f1412ca63cd
-- title:
--   Examples: arrow least
-- statement:
--   `f(⊤, ⊥)` lies below every constructor tree, so `x ≤ ⊥ ∨ f(⊤, ⊥) ≤ x` holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L121-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L121-L131

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

theorem DeciSigma1.Examples.arrow_least :
    DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![2, 1]) leastQueries := by sorry
