-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_tendsto_log_momentNormalized_diagonalKernel_div
-- name    : Ehrhart.BergmanJetPointwiseLogKernel.tendsto_log_momentNormalized_diagonalKernel_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/d0232579-1554-4334-9b8e-74154e3baf53
-- title:
--   Ehrhart.BergmanJetPointwiseLogKernel.tendsto_log_momentNormalized_diagonalKernel_div
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

theorem Ehrhart.BergmanJetPointwiseLogKernel.tendsto_log_momentNormalized_diagonalKernel_div
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) :
    Tendsto
      (fun k : ℕ =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      atTop (𝓝 (momentNormalizedPotential F x)) := by sorry
