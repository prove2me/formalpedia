-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentTorusRepresentative_jetBasis
-- name    : Ehrhart.BergmanJetTorusSlopeBridge.integral_momentTorusRepresentative_jetBasis
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/f05abf22-5ff2-4e11-8f8d-227b86dff9e3
-- title:
--   Ehrhart.BergmanJetTorusSlopeBridge.integral_momentTorusRepresentative_jetBasis
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
open Ehrhart.BergmanJetTorusSlopeBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open TorusCharacters WeightedTorusHilbert BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge JetEnvelopeRightDerivative
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetTorusSlopeBridge.integral_momentTorusRepresentative_jetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (i : Fin (bergmanDimension K k)) :
    (∫ q : LogTorus n,
      Complex.normSq (momentTorusRepresentative
        K hk F htransport
          (momentSimultaneousJetBasis
            K hk F htransport p i) q)
        ∂(weightedTorusMeasure k
          (momentNormalizedPotential F))) = 1 := by sorry
