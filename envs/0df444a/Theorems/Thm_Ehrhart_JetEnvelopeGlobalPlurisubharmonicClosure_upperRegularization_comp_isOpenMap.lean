-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_upperRegularization_comp_isOpenMap
-- name    : Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.upperRegularization_comp_isOpenMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/f903f9fd-dcf4-4d4d-a0f5-ed5e1f51331e
-- title:
--   Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.upperRegularization_comp_isOpenMap
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
open Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
open Set Filter Function MeasureTheory Metric
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope ActualJetPlurisubharmonicClosure
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace

theorem Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.upperRegularization_comp_isOpenMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (g : X → Y)
    (hg : Continuous g) (ho : IsOpenMap g) (x : X) :
    upperRegularization (fun y : X => f (g y)) x =
      upperRegularization f (g x) := by sorry
