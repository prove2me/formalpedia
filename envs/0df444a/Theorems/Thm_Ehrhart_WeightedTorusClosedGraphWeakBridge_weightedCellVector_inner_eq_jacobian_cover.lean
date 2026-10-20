-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellVector_inner_eq_jacobian_cover
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellVector_inner_eq_jacobian_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/debb5773-1e8d-4fec-96f6-8ecd8f1a1efb
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellVector_inner_eq_jacobian_cover
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

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellVector_inner_eq_jacobian_cover {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : weightedTorusFormL2 k φ) :
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun p : WeightedTorusHilbert.LogTorus n =>
                (f p : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ))
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by sorry
