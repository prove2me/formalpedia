-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalSchwarzRatio_sq_mul_exp_le_one
-- name    : Ehrhart.JetEnvelopeLocalGrowth.sourceLocalSchwarzRatio_sq_mul_exp_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/3fa783a5-d0f5-4e57-9d69-7f88a77a6533
-- title:
--   Ehrhart.JetEnvelopeLocalGrowth.sourceLocalSchwarzRatio_sq_mul_exp_le_one
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
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v

theorem Ehrhart.JetEnvelopeLocalGrowth.sourceLocalSchwarzRatio_sq_mul_exp_le_one
    {d R t : ℝ} (hd : 0 ≤ d) (hR : 0 < R)
    (hshrinking : d < R * Real.exp (-t / 2)) :
    (d / R) ^ 2 * Real.exp t ≤ 1 := by sorry
