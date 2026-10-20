-- Prove2me | Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularSourceRadialCutoff_smul_L2_tendsto
-- name    : Ehrhart.TorusFriedrichsCutoff.angularSourceRadialCutoff_smul_L2_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/6dcba4b1-2022-471a-9280-2a675122dc62
-- title:
--   Ehrhart.TorusFriedrichsCutoff.angularSourceRadialCutoff_smul_L2_tendsto
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
open Ehrhart.TorusFriedrichsCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff

theorem Ehrhart.TorusFriedrichsCutoff.angularSourceRadialCutoff_smul_L2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        (angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q))
      atTop (nhds (hF.toLp F)) := by sorry
