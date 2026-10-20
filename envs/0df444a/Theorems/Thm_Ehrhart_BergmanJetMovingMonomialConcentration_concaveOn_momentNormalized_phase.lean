-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingMonomialConcentration_concaveOn_momentNormalized_phase
-- name    : Ehrhart.BergmanJetMovingMonomialConcentration.concaveOn_momentNormalized_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/d5d74c70-6d07-41a8-94b4-56cc30aeea89
-- title:
--   Ehrhart.BergmanJetMovingMonomialConcentration.concaveOn_momentNormalized_phase
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
open Ehrhart.BergmanJetMovingMonomialConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetMovingMonomialConcentration.concaveOn_momentNormalized_phase
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u : Space n) :
    ConcaveOn ℝ Set.univ
      (phase u (momentNormalizedPotential F)) := by sorry
