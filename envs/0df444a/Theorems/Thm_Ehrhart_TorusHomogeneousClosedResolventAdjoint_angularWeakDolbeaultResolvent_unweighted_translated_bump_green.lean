-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousClosedResolventAdjoint_angularWeakDolbeaultResolvent_unweighted_translated_bump_green
-- name    : Ehrhart.TorusHomogeneousClosedResolventAdjoint.angularWeakDolbeaultResolvent_unweighted_translated_bump_green
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/4619fac7-8199-4610-ade6-2f0cff53f0d6
-- title:
--   Ehrhart.TorusHomogeneousClosedResolventAdjoint.angularWeakDolbeaultResolvent_unweighted_translated_bump_green
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
open Ehrhart.TorusHomogeneousClosedResolventAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusHomogeneousClosedResolventAdjoint.angularWeakDolbeaultResolvent_unweighted_translated_bump_green
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
          (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j *
        (conj (barPartialCoordinate
          (fun z : LogSpace n =>
            ((complexShrinkingBump (n := n) k).normed
              (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ) *
            holomorphicCoordinate
              (fun z : LogSpace n =>
                (angularCoverPotential a z : ℂ)) y j)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      ((f - angularWeakScalarResolventCLM a f)
        (complexTorusCoverProjection n y)) *
        ((complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) (x - y) : ℂ)
      ∂(volume : Measure (LogSpace n))) := by sorry
