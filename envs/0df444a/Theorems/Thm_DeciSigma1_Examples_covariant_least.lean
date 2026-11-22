-- Prove2me | Theorems.Thm_DeciSigma1_Examples_covariant_least
-- name    : DeciSigma1.Examples.covariant_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:55.063353+00:00
-- url     : https://prove2.me/theorems/975253e4-eb27-40a4-8739-b4a540b08afb
-- title:
--   Examples: covariant least
-- statement:
--   When both arguments are covariant, `x ≤ ⊥ ∨ f(⊥, ⊥) ≤ x` holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L172-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L172-L183

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

theorem DeciSigma1.Examples.covariant_least :
    DeciSigma1.Full.DisjEntailsIn (fun _ => True) (fun _ => false)
        (pinned ![1, 1]) leastQueries := by sorry
