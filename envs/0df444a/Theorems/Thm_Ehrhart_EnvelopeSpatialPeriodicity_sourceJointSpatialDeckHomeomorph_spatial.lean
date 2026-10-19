-- Prove2me | Theorems.Thm_Ehrhart_EnvelopeSpatialPeriodicity_sourceJointSpatialDeckHomeomorph_spatial
-- name    : Ehrhart.EnvelopeSpatialPeriodicity.sourceJointSpatialDeckHomeomorph_spatial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/c3feb811-26c1-4d54-a9a6-2e85f6919649
-- title:
--   Ehrhart.EnvelopeSpatialPeriodicity.sourceJointSpatialDeckHomeomorph_spatial
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

theorem Ehrhart.EnvelopeSpatialPeriodicity.sourceJointSpatialDeckHomeomorph_spatial
    {n : ℕ} (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    (sourceJointSpatialDeckHomeomorph m q).val.1 =
      q.val.1 + TorusCharacters.imaginaryShift m := by sorry
