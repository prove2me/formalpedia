-- Prove2me | Theorems.Thm_Ehrhart_MomentWeakBergmanProbabilityEndpoint_momentNormalizedDensity_div_volume_eq_gibbsDensity
-- name    : Ehrhart.MomentWeakBergmanProbabilityEndpoint.momentNormalizedDensity_div_volume_eq_gibbsDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/0e8f8217-48c7-4733-8f86-a8434b7dd59b
-- title:
--   Ehrhart.MomentWeakBergmanProbabilityEndpoint.momentNormalizedDensity_div_volume_eq_gibbsDensity
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
open Ehrhart.MomentWeakBergmanProbabilityEndpoint
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman MomentWeakGlobalKernel
open scoped BigOperators ENNReal Topology

theorem Ehrhart.MomentWeakBergmanProbabilityEndpoint.momentNormalizedDensity_div_volume_eq_gibbsDensity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (x : Space n) :
    Real.exp (-momentNormalizedPotential F x) /
        normalizedVolume K.carrier =
      WeightedPoincare.normalizedDensity F.potential x := by sorry
