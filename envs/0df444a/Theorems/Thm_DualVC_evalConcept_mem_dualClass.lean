-- Prove2me | Theorems.Thm_DualVC_evalConcept_mem_dualClass
-- name    : DualVC.evalConcept_mem_dualClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:39.418868+00:00
-- url     : https://prove2.me/theorems/94335832-129c-4b42-a8e5-0ec6ba8a94b2
-- title:
--   Dual VC: eval Concept mem dual Class
-- statement:
--   Membership lemma for Assouad's dual VC construction: the evaluation function
--   `fun c => c x` belongs to the dual class `C^T` of `C`. Used in the bitstring coding
--   step of the dual bound `vcDim(C^T) ≤ 2^(vcDim(C) + 1) - 1`, the standard inequality
--   that lets compression arguments switch between primal and dual without losing
--   dimension control.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L55-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L55-L56

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_DualVC
set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open DualVC
variable {X : Type u} {C : ConceptClass X Bool}

theorem DualVC.evalConcept_mem_dualClass (x : X) : evalConcept x ∈ DualClass X C := by sorry
