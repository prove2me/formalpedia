-- Prove2me | Theorems.Thm_DeciSigma1_Examples_postFixedPoint_regular
-- name    : DeciSigma1.Examples.postFixedPoint_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:28:07.720345+00:00
-- url     : https://prove2.me/theorems/56e97727-3963-4987-907f-41d23f79554a
-- title:
--   Examples: post Fixed Point regular
-- statement:
--   The tree all of whose paths are constructor positions is regular and satisfies
--   `f(x) ≤ x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L68-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L68-L69

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.postFixedPoint_regular : postFixedPoint.HoldsIn IsRegularTree := by sorry
