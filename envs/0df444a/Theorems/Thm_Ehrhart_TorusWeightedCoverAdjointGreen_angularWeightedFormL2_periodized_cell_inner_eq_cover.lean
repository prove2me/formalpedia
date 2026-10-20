-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_angularWeightedFormL2_periodized_cell_inner_eq_cover
-- name    : Ehrhart.TorusWeightedCoverAdjointGreen.angularWeightedFormL2_periodized_cell_inner_eq_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/f51bd329-1974-4e9b-8dcc-d7f150cc4e47
-- title:
--   Ehrhart.TorusWeightedCoverAdjointGreen.angularWeightedFormL2_periodized_cell_inner_eq_cover
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

theorem Ehrhart.TorusWeightedCoverAdjointGreen.angularWeightedFormL2_periodized_cell_inner_eq_cover
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (W : angularWeightedFormL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by sorry
