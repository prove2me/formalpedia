-- Prove2me | Theorems.Thm_Ehrhart_TorusMollifiedBochner_sourceTorusClosedForm_barPartial
-- name    : Ehrhart.TorusMollifiedBochner.sourceTorusClosedForm_barPartial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/121b3942-c732-43d6-9690-59e8b55d3631
-- title:
--   Ehrhart.TorusMollifiedBochner.sourceTorusClosedForm_barPartial
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
open Ehrhart.TorusMollifiedBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusDistributionBridge TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusMollifiedBochner.sourceTorusClosedForm_barPartial
    {n : ℕ}
    {F : LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F) :
    ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial
          (fun z => barPartialCoordinate F z i) j q) := by sorry
