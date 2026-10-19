-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingPhaseConcentration_exists_momentNormalized_phase_gap_outside_ball
-- name    : Ehrhart.BergmanJetMovingPhaseConcentration.exists_momentNormalized_phase_gap_outside_ball
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/574233dd-7d75-4558-afd4-da5022fbaa60
-- title:
--   Ehrhart.BergmanJetMovingPhaseConcentration.exists_momentNormalized_phase_gap_outside_ball
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
open Ehrhart.BergmanJetMovingPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetPhaseLaplace
open BergmanJetDualPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetMovingPhaseConcentration.exists_momentNormalized_phase_gap_outside_ball
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) x₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : Space n,
      x ∉ Metric.ball x₀ r →
        phase u (momentNormalizedPotential F) x ≤
          phase u (momentNormalizedPotential F) x₀ - η := by sorry
