-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
-- name    : Ehrhart.TorusWeightedCoverAdjointGreen.angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/f634ff35-580d-49b8-a133-a14dee943d1f
-- title:
--   Ehrhart.TorusWeightedCoverAdjointGreen.angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
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
open Ehrhart.TorusWeightedCoverAdjointGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBochner WeightedTorusBrascampLieb TorusDeckPeriodization
open TorusDeckGraphAdjoint TorusDeckFundamentalCell TorusDeckFullCellDerivative
open TorusDeckWeightedUnfolding
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

theorem Ehrhart.TorusWeightedCoverAdjointGreen.angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
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
