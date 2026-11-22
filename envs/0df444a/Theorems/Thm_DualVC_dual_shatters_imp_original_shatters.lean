-- Prove2me | Theorems.Thm_DualVC_dual_shatters_imp_original_shatters
-- name    : DualVC.dual_shatters_imp_original_shatters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:46.571341+00:00
-- url     : https://prove2.me/theorems/6ae5397d-d31b-4558-996f-692201fc2c96
-- title:
--   Dual VC: dual shatters imp original shatters
-- statement:
--   Core coding lemma (Assouad 1983): if the dual class shatters a set `S`
--       of concepts with `|S| ≥ 2^(d+1)`, then the original class shatters
--       some set of `d+1` points.
--
--       Proof: index `2^(d+1)` concepts by bitstrings `b : Fin (d+1) → Bool`.
--       For each coordinate `j`, dual shattering provides a point `x_j` that
--       "reads off" the `j`-th bit. Then `{x_0, ..., x_d}` is shattered by `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L65-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L65-L136

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

theorem DualVC.dual_shatters_imp_original_shatters {d : ℕ}
    (S : Finset ↥C) (hS : Shatters ↥C (DualClass X C) S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset X, T.card = d + 1 ∧ Shatters X C T := by sorry
