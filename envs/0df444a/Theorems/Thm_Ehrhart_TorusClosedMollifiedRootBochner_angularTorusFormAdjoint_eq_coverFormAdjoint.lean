-- Prove2me | Theorems.Thm_Ehrhart_TorusClosedMollifiedRootBochner_angularTorusFormAdjoint_eq_coverFormAdjoint
-- name    : Ehrhart.TorusClosedMollifiedRootBochner.angularTorusFormAdjoint_eq_coverFormAdjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/b8507e21-67b6-40a5-8e3c-bf8b2851cce7
-- title:
--   Ehrhart.TorusClosedMollifiedRootBochner.angularTorusFormAdjoint_eq_coverFormAdjoint
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
open Ehrhart.TorusClosedMollifiedRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusClosedMollifiedRootBochner.angularTorusFormAdjoint_eq_coverFormAdjoint
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n) (q : LogTorus n) :
    angularTorusFormAdjoint a V q =
      coverFormAdjoint (angularCoverPotential a) V
        (sourceTorusCoverPoint q) := by sorry
