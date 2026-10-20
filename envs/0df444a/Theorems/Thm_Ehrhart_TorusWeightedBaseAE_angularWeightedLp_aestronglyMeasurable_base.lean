-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedLp_aestronglyMeasurable_base
-- name    : Ehrhart.TorusWeightedBaseAE.angularWeightedLp_aestronglyMeasurable_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/b947a9ec-c20f-4032-b91a-dfcce093c775
-- title:
--   Ehrhart.TorusWeightedBaseAE.angularWeightedLp_aestronglyMeasurable_base
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
open Ehrhart.TorusWeightedBaseAE
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusWeightedBaseAE.angularWeightedLp_aestronglyMeasurable_base
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    AEStronglyMeasurable
      (fun p : LogTorus n => f p)
      (sourceTorusBaseMeasure n) := by sorry
