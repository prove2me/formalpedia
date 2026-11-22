-- Prove2me | Theorems.Thm_DeciSigma1_Examples_not_comparable_binary
-- name    : DeciSigma1.Examples.not_comparable_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:28:01.905132+00:00
-- url     : https://prove2.me/theorems/79ef80e7-9afb-40f9-a7f0-87cad44dd1db
-- title:
--   Examples: not comparable binary
-- statement:
--   Over binary trees, `f(f(⊥, ⊥), ⊥)` and `f(⊥, f(⊥, ⊥))` are incomparable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L55-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L55-L60

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.not_comparable_binary : ¬ (comparable 2).HoldsIn (fun _ => True) := by sorry
