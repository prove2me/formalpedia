-- Prove2me | Theorems.Thm_Ehrhart_EnvelopeSpatialPeriodicity_sourcePositiveJointTimePoint_spatial_translate
-- name    : Ehrhart.EnvelopeSpatialPeriodicity.sourcePositiveJointTimePoint_spatial_translate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/5983bd8c-977f-4e49-acd5-c4b1b0c6d621
-- title:
--   Ehrhart.EnvelopeSpatialPeriodicity.sourcePositiveJointTimePoint_spatial_translate
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
open Ehrhart.EnvelopeSpatialPeriodicity
open Set Function Filter MeasureTheory
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology

theorem Ehrhart.EnvelopeSpatialPeriodicity.sourcePositiveJointTimePoint_spatial_translate
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    sourcePositiveJointTimePoint
        (z + TorusCharacters.imaginaryShift m) t ht =
      sourceJointSpatialDeckHomeomorph m
        (sourcePositiveJointTimePoint z t ht) := by sorry
