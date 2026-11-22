-- Prove2me | Theorems.Thm_DeciSigma1_Examples_arrow_not_least
-- name    : DeciSigma1.Examples.arrow_not_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:26.568871+00:00
-- url     : https://prove2.me/theorems/a3120a06-6237-45c1-9b0c-76047a6b12a1
-- title:
--   Examples: arrow not least
-- statement:
--   With the same variance, `x ≤ ⊥ ∨ f(⊥, ⊥) ≤ x` is not entailed: `x = f(⊤, ⊥)` refutes
--   both disjuncts, since `f(⊥, ⊥) ≤ f(⊤, ⊥)` would need `⊤ ≤ ⊥`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L153-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L153-L169

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

theorem DeciSigma1.Examples.arrow_not_least :
    ¬ DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![1, 1]) leastQueries := by sorry
