-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingMonomialTailConvergence_exists_eventual_momentNormalized_moving_off_ball_exponential
-- name    : Ehrhart.BergmanJetMovingMonomialTailConvergence.exists_eventual_momentNormalized_moving_off_ball_exponential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/7567a174-b705-4a9f-8ca6-527cb5870302
-- title:
--   Ehrhart.BergmanJetMovingMonomialTailConvergence.exists_eventual_momentNormalized_moving_off_ball_exponential
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
open Ehrhart.BergmanJetMovingMonomialTailConvergence
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetPointwiseLogKernel
open BergmanJetMovingPhaseConcentration BergmanJetMovingMonomialConcentration
open BergmanJetMovingMonomialProbability
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetMovingMonomialTailConvergence.exists_eventual_momentNormalized_moving_off_ball_exponential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    {r : ℝ} (hr : 0 < r) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ᶠ k : ℕ in atTop,
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
            monomialIntegral (k : ℝ) (u k)
              (momentNormalizedPotential F) ≤
          A * Real.exp (-((k : ℝ) * (η / 2))) := by sorry
