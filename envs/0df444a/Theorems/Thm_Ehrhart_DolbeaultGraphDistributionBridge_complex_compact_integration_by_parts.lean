-- Prove2me | Theorems.Thm_Ehrhart_DolbeaultGraphDistributionBridge_complex_compact_integration_by_parts
-- name    : Ehrhart.DolbeaultGraphDistributionBridge.complex_compact_integration_by_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/4e2025e7-0988-49d3-a539-bf0d25b41d84
-- title:
--   Ehrhart.DolbeaultGraphDistributionBridge.complex_compact_integration_by_parts
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
open Ehrhart.DolbeaultGraphDistributionBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths DolbeaultRegularity
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

theorem Ehrhart.DolbeaultGraphDistributionBridge.complex_compact_integration_by_parts {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      F z * ((fderiv ℝ ψ z) v : ℂ)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(∫ z : TorusCharacters.LogSpace n,
        (fderiv ℝ F z) v * (ψ z : ℂ)
        ∂(volume : Measure (TorusCharacters.LogSpace n))) := by sorry
