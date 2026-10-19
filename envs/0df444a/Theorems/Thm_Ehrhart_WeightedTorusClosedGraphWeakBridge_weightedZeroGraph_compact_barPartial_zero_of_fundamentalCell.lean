-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/912e1d56-81e8-47f4-98ad-459da1ac490d
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
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

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ)) ∈
      functionDolbeaultGraph k φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
          coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) = 0 := by sorry
