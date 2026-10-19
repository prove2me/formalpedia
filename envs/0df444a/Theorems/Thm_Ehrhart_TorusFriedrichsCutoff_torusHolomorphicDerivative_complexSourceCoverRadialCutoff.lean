-- Prove2me | Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_torusHolomorphicDerivative_complexSourceCoverRadialCutoff
-- name    : Ehrhart.TorusFriedrichsCutoff.torusHolomorphicDerivative_complexSourceCoverRadialCutoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/e5fc93d8-e600-4611-a263-4843df38af5d
-- title:
--   Ehrhart.TorusFriedrichsCutoff.torusHolomorphicDerivative_complexSourceCoverRadialCutoff
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

theorem Ehrhart.TorusFriedrichsCutoff.torusHolomorphicDerivative_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) (i : Fin n) (q : LogTorus n) :
    torusScalarRepresentative
      (fun z => holomorphicCoordinate
        (complexSourceCoverRadialCutoff m) z i) q =
      conj (sourceTorusBarPartial
        (complexSourceCoverRadialCutoff m) i q) := by sorry
