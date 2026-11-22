-- Prove2me | Theorems.Thm_DeciSigma1_Examples_not_fixedPoint_finite
-- name    : DeciSigma1.Examples.not_fixedPoint_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:29:08.681114+00:00
-- url     : https://prove2.me/theorems/3ec38d91-4ba0-4f62-8791-a8037c62632f
-- title:
--   Examples: not fixed Point finite
-- statement:
--   No finite tree satisfies `x = f(x)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L118-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L118-L123

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.not_fixedPoint_finite : ¬ fixedPoint.HoldsIn FiniteTop (fun _ => true) := by sorry
