-- Prove2me | Theorems.Thm_DeciSigma1_Examples_not_postFixedPoint_finite
-- name    : DeciSigma1.Examples.not_postFixedPoint_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:27:44.758713+00:00
-- url     : https://prove2.me/theorems/b133f388-700c-4196-af85-25bb5a197fcd
-- title:
--   Examples: not post Fixed Point finite
-- statement:
--   A unary tree `t` with `f(t) ≤ t` contains every path, so no finite tree satisfies
--   `f(x) ≤ x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L73-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L73-L81

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.not_postFixedPoint_finite : ¬ postFixedPoint.HoldsIn IsFiniteTree := by sorry
