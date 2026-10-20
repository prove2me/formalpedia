-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_sourceTorusBarPartial_cutoffPhysicalField
-- name    : Ehrhart.MatrixTorusBochnerCoreApproximation.sourceTorusBarPartial_cutoffPhysicalField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/d7fa2424-7e60-4e25-8c80-115a3296f897
-- title:
--   Ehrhart.MatrixTorusBochnerCoreApproximation.sourceTorusBarPartial_cutoffPhysicalField
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
open Ehrhart.MatrixTorusBochnerCoreApproximation
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.MatrixTorusBochnerCoreApproximation.sourceTorusBarPartial_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (i j : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusBarPartial
      (fun z => cutoffPhysicalField m W z i) j p =
      (sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z i) j p +
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial
          (complexSourceCoverRadialCutoff m) j p := by sorry
