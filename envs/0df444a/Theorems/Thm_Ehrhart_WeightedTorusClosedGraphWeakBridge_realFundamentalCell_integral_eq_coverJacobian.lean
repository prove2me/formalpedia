-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCell_integral_eq_coverJacobian
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.realFundamentalCell_integral_eq_coverJacobian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/c579d0fc-0f3a-4e71-8dec-7f61f43289ce
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.realFundamentalCell_integral_eq_coverJacobian
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
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.realFundamentalCell_integral_eq_coverJacobian {n : ℕ}
    (b : Space n)
    (g : TorusCharacters.LogSpace n → ℂ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
      ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n, g z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by sorry
