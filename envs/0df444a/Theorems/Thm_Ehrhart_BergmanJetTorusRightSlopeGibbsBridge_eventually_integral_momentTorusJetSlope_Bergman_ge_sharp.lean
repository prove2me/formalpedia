-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
-- name    : Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/56385971-b746-4e4a-b053-50a546e1506f
-- title:
--   Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
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
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentTorusJetSlope K F htransport p k q
            ∂(momentTorusBergmanProbability K F k) := by sorry
