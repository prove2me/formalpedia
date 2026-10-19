-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularDolbeaultGraph_compact_barPartial_green
-- name    : Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_compact_barPartial_green
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/2283dbba-4406-49ad-a114-39d2f3343ae3
-- title:
--   Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_compact_barPartial_green
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

theorem Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_compact_barPartial_green
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (∫ z : LogSpace n,
      complexTorusCoverLift (fun q : LogTorus n => f q) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (LogSpace n))) := by sorry
