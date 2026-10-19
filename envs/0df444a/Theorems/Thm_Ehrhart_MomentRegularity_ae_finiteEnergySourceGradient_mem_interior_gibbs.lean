-- Prove2me | Theorems.Thm_Ehrhart_MomentRegularity_ae_finiteEnergySourceGradient_mem_interior_gibbs
-- name    : Ehrhart.MomentRegularity.ae_finiteEnergySourceGradient_mem_interior_gibbs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/5ede2af9-fe4e-49d3-bf90-9ab1f6271605
-- title:
--   Ehrhart.MomentRegularity.ae_finiteEnergySourceGradient_mem_interior_gibbs
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
open Ehrhart.MomentRegularity
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology

theorem Ehrhart.MomentRegularity.ae_finiteEnergySourceGradient_mem_interior_gibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
        F.potential x ∈ interior K.carrier := by sorry
