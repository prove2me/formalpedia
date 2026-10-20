-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_eventually_integral_momentPositiveTorusJetSlope_ge_sharp
-- name    : Ehrhart.BergmanJetTorusSlopeBridge.eventually_integral_momentPositiveTorusJetSlope_ge_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/977e05ab-d60b-4e76-8d56-2afe89412caf
-- title:
--   Ehrhart.BergmanJetTorusSlopeBridge.eventually_integral_momentPositiveTorusJetSlope_ge_sharp
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

theorem Ehrhart.BergmanJetTorusSlopeBridge.eventually_integral_momentPositiveTorusJetSlope_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hk : 0 < k,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentPositiveTorusJetSlope
            K hk F htransport p
            (Nat.floor
              (BodyScale.canonicalScale K * (k : ℝ))) q
          ∂(momentTorusBergmanProbability K F k) := by sorry
