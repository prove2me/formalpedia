-- Prove2me | Theorems.Thm_Ehrhart_MomentWeakBergmanProbabilityEndpoint_normalizedMonomialDensity_momentNormalized_pos
-- name    : Ehrhart.MomentWeakBergmanProbabilityEndpoint.normalizedMonomialDensity_momentNormalized_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/50691b5c-ebbd-4349-8b58-5683ac7bfd74
-- title:
--   Ehrhart.MomentWeakBergmanProbabilityEndpoint.normalizedMonomialDensity_momentNormalized_pos
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

theorem Ehrhart.MomentWeakBergmanProbabilityEndpoint.normalizedMonomialDensity_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    0 < normalizedMonomialDensity
      K k (momentNormalizedPotential F) u x := by sorry
