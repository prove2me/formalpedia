-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingMonomialProbability_exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
-- name    : Ehrhart.BergmanJetMovingMonomialProbability.exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/a6a7a1af-2b86-4ed9-843c-7aac599e6957
-- title:
--   Ehrhart.BergmanJetMovingMonomialProbability.exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
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
open Ehrhart.BergmanJetMovingMonomialProbability
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetMovingMonomialProbability.exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x₀ : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧
      0 < (volume : Measure (Space n)).real
        (Metric.ball x₀ r) ∧
      ∀ᶠ j : ℕ in atTop, ∀ {k : ℝ}, 0 < k →
        (volume : Measure (Space n)).real
            (Metric.ball x₀ r) *
          Real.exp
            (k *
              (phase (u j) (momentNormalizedPotential F) x₀ - ε)) ≤
        monomialIntegral k (u j) (momentNormalizedPotential F) := by sorry
