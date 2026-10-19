-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_integral_finiteEnergySourceLegendreGradient_target
-- name    : Ehrhart.BergmanJetDualGradientInverseTransport.integral_finiteEnergySourceLegendreGradient_target
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/b15e6251-465a-461a-8cda-c608f0e0f78c
-- title:
--   Ehrhart.BergmanJetDualGradientInverseTransport.integral_finiteEnergySourceLegendreGradient_target
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
open Ehrhart.BergmanJetDualGradientInverseTransport
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentWeakFirstVariation MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetDualGradientConcentration
open BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology

theorem Ehrhart.BergmanJetDualGradientInverseTransport.integral_finiteEnergySourceLegendreGradient_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u : Space n,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(normalizedTargetBodyMeasure K)) =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by sorry
