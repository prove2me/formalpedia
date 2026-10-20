-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_measurableSet_sourceLocalTorusBox
-- name    : Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourceLocalTorusBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/ad791e47-1023-41f7-98cb-390150f0e042
-- title:
--   Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourceLocalTorusBox
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

theorem Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourceLocalTorusBox (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalTorusBox n δ) := by sorry
