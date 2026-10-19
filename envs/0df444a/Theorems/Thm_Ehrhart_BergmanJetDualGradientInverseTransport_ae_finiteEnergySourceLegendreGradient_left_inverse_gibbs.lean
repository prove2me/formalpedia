-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
-- name    : Ehrhart.BergmanJetDualGradientInverseTransport.ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/3324db91-ea35-4778-b1f9-027d17f3676f
-- title:
--   Ehrhart.BergmanJetDualGradientInverseTransport.ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
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

theorem Ehrhart.BergmanJetDualGradientInverseTransport.ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) = x := by sorry
