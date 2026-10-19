-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularCellWeakAdjointFunctional_apply
-- name    : Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/34d6f114-937b-47c0-aaa8-e0dcc35f92bb
-- title:
--   Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_apply
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
open Ehrhart.WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold

theorem Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_apply {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : angularDolbeaultGraphAmbient a) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j v =
      @inner ℂ (angularWeightedCellScalarL2 a b) _
        (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
        (angularScalarFundamentalLiftLI ha b (WithLp.fst v)) +
      @inner ℂ (angularWeightedCellFormL2 a b) _
        (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
        (angularFormFundamentalLiftLI ha b (WithLp.snd v)) := by sorry
