-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_eventually_momentNormalized_moving_phase_le_max_add
-- name    : Ehrhart.BergmanJetPointwiseLogKernel.eventually_momentNormalized_moving_phase_le_max_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/9c06757b-8e96-4cb4-be67-89eb4a16e178
-- title:
--   Ehrhart.BergmanJetPointwiseLogKernel.eventually_momentNormalized_moving_phase_le_max_add
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
open Ehrhart.BergmanJetPointwiseLogKernel
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability BergmanMonomials MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open MomentWeakGlobalKernel BergmanJetPhaseLaplace BergmanJetMonomialEnvelopeLower
open MomentMoserTrudinger SpatialBergmanPointwiseAsymptotics
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetPointwiseLogKernel.eventually_momentNormalized_moving_phase_le_max_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u₀ (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
      phase (u k) (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x + ε := by sorry
