-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellScalar_inner_eq_unweighted
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellScalar_inner_eq_unweighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/45dcc640-12d6-4841-b06d-3dba49e377ad
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellScalar_inner_eq_unweighted
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

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellScalar_inner_eq_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : weightedTorusScalarL2 k φ) :
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) =
        ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by sorry
