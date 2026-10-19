-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
-- name    : Ehrhart.JetEnvelopeTrueRadialMollifier.eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/a31b2ea2-94cb-42a5-8254-a70af7df29e5
-- title:
--   Ehrhart.JetEnvelopeTrueRadialMollifier.eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
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
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar

theorem Ehrhart.JetEnvelopeTrueRadialMollifier.eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (q : SourceJointComplexCover n)
    (hupper : UpperSemicontinuousAt f q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      sourceJointTrueRadialSmoothed f k q ≤ f q + ε := by sorry
