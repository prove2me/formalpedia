-- Prove2me | Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_jointSourceTorusVelocity_eq_cover
-- name    : Ehrhart.EnvelopeGeneralTorusDescent.jointSourceTorusVelocity_eq_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/1d4f2640-8923-405e-8c91-a08472a6a058
-- title:
--   Ehrhart.EnvelopeGeneralTorusDescent.jointSourceTorusVelocity_eq_cover
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
open Ehrhart.EnvelopeGeneralTorusDescent
open Set Function Filter MeasureTheory
open ComplexKillingSaturationBridge MatrixTorusBochnerIdentity JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative EnvelopeSmoothing EnvelopeTorusDescent
open scoped Topology ContDiff

theorem Ehrhart.EnvelopeGeneralTorusDescent.jointSourceTorusVelocity_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusVelocity F t q =
      jointSourceCoverVelocity F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by sorry
