-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_exists_eventual_momentNormalized_uniform_moving_phase_coercivity
-- name    : Ehrhart.BergmanJetPointwiseLogKernel.exists_eventual_momentNormalized_uniform_moving_phase_coercivity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/7ec4e765-95b3-4488-bd73-1a9d3d84336b
-- title:
--   Ehrhart.BergmanJetPointwiseLogKernel.exists_eventual_momentNormalized_uniform_moving_phase_coercivity
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

theorem Ehrhart.BergmanJetPointwiseLogKernel.exists_eventual_momentNormalized_uniform_moving_phase_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀)) :
    ∃ d C : ℝ, 0 < d ∧
      ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
        phase (u k) (momentNormalizedPotential F) z ≤
          C - d * ‖z‖ := by sorry
