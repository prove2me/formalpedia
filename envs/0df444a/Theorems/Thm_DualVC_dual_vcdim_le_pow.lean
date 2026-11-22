-- Prove2me | Theorems.Thm_DualVC_dual_vcdim_le_pow
-- name    : DualVC.dual_vcdim_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:32.287564+00:00
-- url     : https://prove2.me/theorems/d29b437a-936e-4aea-9f58-e0a181b811d2
-- title:
--   Dual VC: dual vcdim le pow
-- statement:
--   **Assouad's dual VC bound**: if `VCDim(C) ≤ d`, then the VC dimension of
--       the dual class is at most `2^(d+1) - 1`.
--
--       This is tight: the class of all subsets of `{1,...,d}` achieves equality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L142-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean#L142-L159

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

theorem DualVC.dual_vcdim_le_pow {d : ℕ} (hd : VCDim X C ≤ ↑d) :
    VCDim ↥C (DualClass X C) ≤ ↑(2 ^ (d + 1) - 1) := by sorry
