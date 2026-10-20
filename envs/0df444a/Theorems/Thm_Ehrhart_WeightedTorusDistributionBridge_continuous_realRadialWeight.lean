-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_continuous_realRadialWeight
-- name    : Ehrhart.WeightedTorusDistributionBridge.continuous_realRadialWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/dea8db38-27a0-43c1-a02b-c0de4fc19986
-- title:
--   Ehrhart.WeightedTorusDistributionBridge.continuous_realRadialWeight
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
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906

theorem Ehrhart.WeightedTorusDistributionBridge.continuous_realRadialWeight {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous
      (fun z : WeightedTorusHilbert.LogTorus n =>
        Real.exp (-(k : ℝ) * φ z.1)) := by sorry
