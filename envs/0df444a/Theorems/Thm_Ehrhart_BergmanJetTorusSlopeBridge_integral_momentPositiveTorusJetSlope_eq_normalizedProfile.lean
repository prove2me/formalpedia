-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentPositiveTorusJetSlope_eq_normalizedProfile
-- name    : Ehrhart.BergmanJetTorusSlopeBridge.integral_momentPositiveTorusJetSlope_eq_normalizedProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/86e6cb31-531c-480c-a31a-367b544b975e
-- title:
--   Ehrhart.BergmanJetTorusSlopeBridge.integral_momentPositiveTorusJetSlope_eq_normalizedProfile
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

theorem Ehrhart.BergmanJetTorusSlopeBridge.integral_momentPositiveTorusJetSlope_eq_normalizedProfile
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentPositiveTorusJetSlope
        K hk F htransport p (Nat.floor (t * (k : ℝ))) q
        ∂(momentTorusBergmanProbability K F k)) =
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by sorry
