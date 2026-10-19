-- Prove2me | Theorems.Thm_Ehrhart_EnvelopeTorusDescent_hasDerivAt_sourceJointTimeEmbedding
-- name    : Ehrhart.EnvelopeTorusDescent.hasDerivAt_sourceJointTimeEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/43f8f541-343e-433e-a0ed-60acef974795
-- title:
--   Ehrhart.EnvelopeTorusDescent.hasDerivAt_sourceJointTimeEmbedding
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
open Ehrhart.EnvelopeTorusDescent
open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeSmoothing
open scoped Topology ContDiff

theorem Ehrhart.EnvelopeTorusDescent.hasDerivAt_sourceJointTimeEmbedding
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sourceJointTimeEmbedding z s)
      (sourceJointTimeDirection n) t := by sorry
