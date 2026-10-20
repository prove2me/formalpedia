-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousResolventGreen_angularWeightedScalarCover_density_inner_integrable
-- name    : Ehrhart.TorusHomogeneousResolventGreen.angularWeightedScalarCover_density_inner_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/5f96edba-cc0e-493a-8e5e-f0707a438939
-- title:
--   Ehrhart.TorusHomogeneousResolventGreen.angularWeightedScalarCover_density_inner_integrable
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
open Ehrhart.TorusHomogeneousResolventGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open TorusDeckWeightedUnfolding TorusWeightedCoverAdjointGreen TorusWeightedCoverGlobalGreen
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

theorem Ehrhart.TorusHomogeneousResolventGreen.angularWeightedScalarCover_density_inner_integrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : Continuous ψ) (hψcompact : HasCompactSupport ψ) :
    Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (f (complexTorusCoverProjection n z)) (ψ z))
      (volume : Measure (LogSpace n)) := by sorry
