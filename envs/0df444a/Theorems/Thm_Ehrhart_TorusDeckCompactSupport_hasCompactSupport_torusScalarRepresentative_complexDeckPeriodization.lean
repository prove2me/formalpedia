-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckCompactSupport_hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
-- name    : Ehrhart.TorusDeckCompactSupport.hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/ae36a0e9-7ba9-4c35-abdb-ae9c0ab3509c
-- title:
--   Ehrhart.TorusDeckCompactSupport.hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
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
open Ehrhart.TorusDeckCompactSupport
open Set Function Filter MeasureTheory Matrix
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open MatrixTorusBochnerIdentity TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusDeckCompactSupport.hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    HasCompactSupport
      (torusScalarRepresentative (complexDeckPeriodization ψ)) := by sorry
