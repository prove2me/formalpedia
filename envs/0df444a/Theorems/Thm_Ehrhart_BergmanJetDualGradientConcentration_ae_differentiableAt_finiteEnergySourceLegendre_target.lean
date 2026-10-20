-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_finiteEnergySourceLegendre_target
-- name    : Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/5d08b6a5-57a7-4c13-9db5-0e3953dcd5f2
-- title:
--   Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_target
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
open Ehrhart.BergmanJetDualGradientConcentration
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology

theorem Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ u : Space n ∂(normalizedTargetBodyMeasure K),
      DifferentiableAt ℝ (legendreTransform F.potential) u := by sorry
