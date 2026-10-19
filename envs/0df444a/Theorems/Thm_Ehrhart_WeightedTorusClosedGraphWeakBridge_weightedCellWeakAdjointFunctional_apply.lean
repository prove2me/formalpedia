-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_apply
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/105182fd-b386-4c46-8d48-369a31c03193
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_apply
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

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_apply {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : functionDolbeaultGraphAmbient k φ) :
    weightedCellWeakAdjointFunctional hφ b hψ hψcompact j v =
      @inner ℂ (weightedCellScalarL2 k φ b) _
        (weightedCellAdjointScalarL2 hφ b hψ hψcompact j)
        (weightedScalarFundamentalLiftLI k φ b (WithLp.fst v)) +
      @inner ℂ (weightedCellFormL2 k φ b) _
        (weightedCellAdjointVectorL2 hφ b hψ hψcompact j)
        (weightedFormFundamentalLiftLI k φ b (WithLp.snd v)) := by sorry
