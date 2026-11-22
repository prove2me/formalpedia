-- Prove2me | Theorems.Thm_DeciSigma1_Examples_comparable_unary
-- name    : DeciSigma1.Examples.comparable_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:59.031808+00:00
-- url     : https://prove2.me/theorems/6e807775-c8b7-4258-9c8b-d0a1c20913fb
-- title:
--   Examples: comparable unary
-- statement:
--   Over unary trees, any two trees are comparable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L47-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L47-L48

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.comparable_unary : (comparable 1).HoldsIn (fun _ => True) := by sorry
