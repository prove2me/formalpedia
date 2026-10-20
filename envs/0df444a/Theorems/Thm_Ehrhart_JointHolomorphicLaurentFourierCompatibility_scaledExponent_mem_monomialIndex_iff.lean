-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_scaledExponent_mem_monomialIndex_iff
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.scaledExponent_mem_monomialIndex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/9140bd71-7703-4fa5-95b5-3ca651807ed5
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.scaledExponent_mem_monomialIndex_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.scaledExponent_mem_monomialIndex_iff
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k) (m : Fin n → ℤ) :
    scaledExponent k m ∈
        LatticeAsymptotics.monomialIndex K k ↔
      scaledExponent k m ∈ interior K.carrier := by sorry
