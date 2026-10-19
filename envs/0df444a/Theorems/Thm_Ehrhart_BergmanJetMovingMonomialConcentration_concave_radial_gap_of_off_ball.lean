-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingMonomialConcentration_concave_radial_gap_of_off_ball
-- name    : Ehrhart.BergmanJetMovingMonomialConcentration.concave_radial_gap_of_off_ball
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/63153668-8efb-435f-9393-07069e73d393
-- title:
--   Ehrhart.BergmanJetMovingMonomialConcentration.concave_radial_gap_of_off_ball
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

theorem Ehrhart.BergmanJetMovingMonomialConcentration.concave_radial_gap_of_off_ball
    {n : ℕ} {f : Space n → ℝ}
    (hconc : ConcaveOn ℝ Set.univ f)
    (x₀ : Space n)
    {r η : ℝ} (hr : 0 < r)
    (hgap : ∀ x : Space n,
      x ∉ Metric.ball x₀ r → f x ≤ f x₀ - η)
    (x : Space n)
    (hx : r ≤ ‖x - x₀‖) :
    f x ≤ f x₀ - (η / r) * ‖x - x₀‖ := by sorry
