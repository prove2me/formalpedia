-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_realFundamentalCell_integral_real_eq_coverJacobian
-- name    : Ehrhart.TorusStrongWeightedTorusDescent.realFundamentalCell_integral_real_eq_coverJacobian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/71623546-91bb-41d5-b4cb-680003d28323
-- title:
--   Ehrhart.TorusStrongWeightedTorusDescent.realFundamentalCell_integral_real_eq_coverJacobian
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

theorem Ehrhart.TorusStrongWeightedTorusDescent.realFundamentalCell_integral_real_eq_coverJacobian
    {n : ℕ} (b : Space n)
    (g : LogSpace n → ℝ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by sorry
