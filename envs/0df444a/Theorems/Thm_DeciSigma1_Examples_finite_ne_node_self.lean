-- Prove2me | Theorems.Thm_DeciSigma1_Examples_finite_ne_node_self
-- name    : DeciSigma1.Examples.finite_ne_node_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:24:40.023807+00:00
-- url     : https://prove2.me/theorems/35c8ec49-54ea-4add-b571-54e3126f1c32
-- title:
--   Examples: finite ne node self
-- statement:
--   No finite unary tree `t` satisfies `t = f(t)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L102-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L102-L115

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.finite_ne_node_self (a : FTree 1) : a.toTree ≠ Semantics.Tree.node (fun _ => a.toTree) := by sorry
