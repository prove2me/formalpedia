-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetStrictRadialRegularizer_ball_momentBodyInteriorRadius_subset
-- name    : Ehrhart.BergmanJetStrictRadialRegularizer.ball_momentBodyInteriorRadius_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/57731d1f-5908-441d-8714-3b2b417508bb
-- title:
--   Ehrhart.BergmanJetStrictRadialRegularizer.ball_momentBodyInteriorRadius_subset
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
open Ehrhart.BergmanJetStrictRadialRegularizer
open Set Function Filter MeasureTheory Matrix
open TorusCharacters SupportFunction LatticeAsymptotics BergmanAsymptotics
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerCore
open WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ENNReal Topology ContDiff MatrixOrder
  ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

theorem Ehrhart.BergmanJetStrictRadialRegularizer.ball_momentBodyInteriorRadius_subset
    {n : ℕ} (K : CenteredBody n) :
    Metric.ball (0 : Space n)
      (momentBodyInteriorRadius K) ⊆ K.carrier := by sorry
