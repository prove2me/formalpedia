-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetRealGeodesic_convexOn_momentJetGeodesic
-- name    : Ehrhart.BergmanJetRealGeodesic.convexOn_momentJetGeodesic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/0cc28e12-0ccf-40fd-b2e5-564456022c81
-- title:
--   Ehrhart.BergmanJetRealGeodesic.convexOn_momentJetGeodesic
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
open Ehrhart.BergmanJetRealGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetRealGeodesic.convexOn_momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) :
    ConvexOn ℝ Set.univ
      (momentJetGeodesic K hk F htransport p N z) := by sorry
