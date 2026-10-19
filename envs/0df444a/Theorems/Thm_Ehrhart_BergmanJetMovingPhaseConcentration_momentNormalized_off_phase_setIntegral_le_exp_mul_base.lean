-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingPhaseConcentration_momentNormalized_off_phase_setIntegral_le_exp_mul_base
-- name    : Ehrhart.BergmanJetMovingPhaseConcentration.momentNormalized_off_phase_setIntegral_le_exp_mul_base
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/cddc7b68-9a3e-4a3a-b65c-4dbf3787ffae
-- title:
--   Ehrhart.BergmanJetMovingPhaseConcentration.momentNormalized_off_phase_setIntegral_le_exp_mul_base
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

theorem Ehrhart.BergmanJetMovingPhaseConcentration.momentNormalized_off_phase_setIntegral_le_exp_mul_base
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {s : Set (Space n)} (hs : MeasurableSet s)
    {M : ℝ}
    (hphase : ∀ x ∈ s,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    (∫ x : Space n in s,
      monomialWeight k u (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) ≤
      Real.exp ((k - 1) * M) *
        monomialIntegral 1 u (momentNormalizedPotential F) := by sorry
