-- Prove2me | Theorems.Thm_DeciSigma1_Examples_comparable_unary_regular
-- name    : DeciSigma1.Examples.comparable_unary_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:27:29.252035+00:00
-- url     : https://prove2.me/theorems/393d085d-7026-4165-81d8-6216c14ddd36
-- title:
--   Examples: comparable unary regular
-- statement:
--   The same holds over regular unary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L51-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L51-L52

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.comparable_unary_regular : (comparable 1).HoldsIn IsRegularTree := by sorry
