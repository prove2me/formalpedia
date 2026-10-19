-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_angularWeightedTorus_integral_real_eq_realFundamentalCell
-- name    : Ehrhart.TorusStrongWeightedTorusDescent.angularWeightedTorus_integral_real_eq_realFundamentalCell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/80d17c52-4e77-47f1-96b0-4163e0920511
-- title:
--   Ehrhart.TorusStrongWeightedTorusDescent.angularWeightedTorus_integral_real_eq_realFundamentalCell
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
open Ehrhart.TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusStrongWeightedTorusDescent.angularWeightedTorus_integral_real_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n)
    {G : LogTorus n → ℝ}
    (hG : AEStronglyMeasurable G (sourceTorusBaseMeasure n)) :
    (∫ q : LogTorus n, G q
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularWeightedTorusDensity a
            (realTorusCoverProjection n p) *
          G (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by sorry
