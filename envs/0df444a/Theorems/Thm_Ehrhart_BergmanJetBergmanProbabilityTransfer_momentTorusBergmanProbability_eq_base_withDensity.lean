-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetBergmanProbabilityTransfer_momentTorusBergmanProbability_eq_base_withDensity
-- name    : Ehrhart.BergmanJetBergmanProbabilityTransfer.momentTorusBergmanProbability_eq_base_withDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/9d2fc42f-e628-4811-917c-722c716c8e36
-- title:
--   Ehrhart.BergmanJetBergmanProbabilityTransfer.momentTorusBergmanProbability_eq_base_withDensity
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
open Ehrhart.BergmanJetBergmanProbabilityTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetBergmanProbabilityTransfer.momentTorusBergmanProbability_eq_base_withDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K) :
    momentTorusBergmanProbability K F k =
      (sourceTorusBaseMeasure n).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal (momentWeakTorusBergmanDensity K F k q)) := by sorry
