-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_momentNormalized_phaseMaximizer_iff
-- name    : Ehrhart.BergmanJetDualPhaseConcentration.momentNormalized_phaseMaximizer_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/82de7ec0-174e-45da-b1c4-b2b863051148
-- title:
--   Ehrhart.BergmanJetDualPhaseConcentration.momentNormalized_phaseMaximizer_iff
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
open Ehrhart.BergmanJetDualPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentInteriorLegendre
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetDualPhaseConcentration.momentNormalized_phaseMaximizer_iff
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u x : Space n) :
    (∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) ↔
    (∀ z : Space n,
      phase u F.potential z ≤ phase u F.potential x) := by sorry
