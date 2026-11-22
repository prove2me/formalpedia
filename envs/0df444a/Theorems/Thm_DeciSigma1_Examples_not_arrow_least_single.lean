-- Prove2me | Theorems.Thm_DeciSigma1_Examples_not_arrow_least_single
-- name    : DeciSigma1.Examples.not_arrow_least_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:26.458842+00:00
-- url     : https://prove2.me/theorems/e3164e2c-25e3-496b-b8fd-5773cfbfe2b9
-- title:
--   Examples: not arrow least single
-- statement:
--   Neither disjunct of `arrow_least` is entailed on its own.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L134-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L134-L149

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

theorem DeciSigma1.Examples.not_arrow_least_single (i : Fin 2) :
    ¬ DeciSigma1.Full.DisjEntailsIn (fun _ => True) arrow (pinned ![2, 1]) ![leastQueries i] := by sorry
