-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBoxMeasure_eq_restrict
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxMeasure_eq_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/3681c2e3-0f80-4638-9084-e7928e6264e1
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxMeasure_eq_restrict
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
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxMeasure_eq_restrict (n : ℕ) :
    angularBoxMeasure n =
      (volume : Measure (Space n)).restrict (angularBox n) := by sorry
