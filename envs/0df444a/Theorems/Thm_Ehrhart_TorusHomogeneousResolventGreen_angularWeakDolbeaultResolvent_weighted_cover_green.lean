-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousResolventGreen_angularWeakDolbeaultResolvent_weighted_cover_green
-- name    : Ehrhart.TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/3a5559e7-5cdf-494d-ac2d-ba88dcc433c5
-- title:
--   Ehrhart.TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
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

theorem Ehrhart.TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ) (hψcompact : HasCompactSupport ψ) :
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
              (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f)
          (complexTorusCoverProjection n z))
        (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) := by sorry
