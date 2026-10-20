-- Prove2me | Theorems.Thm_Ehrhart_MomentRegularity_normalizedTargetBodyMeasure_eq_interior_restrict
-- name    : Ehrhart.MomentRegularity.normalizedTargetBodyMeasure_eq_interior_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/16d519dc-466d-4d70-9676-1fc9cb2eeb93
-- title:
--   Ehrhart.MomentRegularity.normalizedTargetBodyMeasure_eq_interior_restrict
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
open Ehrhart.MomentRegularity
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology

theorem Ehrhart.MomentRegularity.normalizedTargetBodyMeasure_eq_interior_restrict
    {n : ℕ} (K : CenteredBody n) :
    normalizedTargetBodyMeasure K =
      ((volume : Measure (Space n)) K.carrier)⁻¹ •
        ((volume : Measure (Space n)).restrict
          (interior K.carrier)) := by sorry
