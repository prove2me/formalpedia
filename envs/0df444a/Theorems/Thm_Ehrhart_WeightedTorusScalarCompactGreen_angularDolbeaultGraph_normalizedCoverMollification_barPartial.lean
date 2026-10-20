-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularDolbeaultGraph_normalizedCoverMollification_barPartial
-- name    : Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_normalizedCoverMollification_barPartial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/d8e08f0a-67e7-43da-ad1c-4ea7eb3918aa
-- title:
--   Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_normalizedCoverMollification_barPartial
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

theorem Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_normalizedCoverMollification_barPartial
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (normalizedCoverMollification
        (complexTorusCoverLift (fun q : LogTorus n => f q)) k) x j =
      normalizedCoverMollification
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) j)) k x := by sorry
