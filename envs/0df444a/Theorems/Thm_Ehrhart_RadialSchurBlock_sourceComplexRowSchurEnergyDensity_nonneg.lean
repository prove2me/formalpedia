-- Prove2me | Theorems.Thm_Ehrhart_RadialSchurBlock_sourceComplexRowSchurEnergyDensity_nonneg
-- name    : Ehrhart.RadialSchurBlock.sourceComplexRowSchurEnergyDensity_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/4bb9ab8f-cc60-4b4a-9614-a637e95ec8b7
-- title:
--   Ehrhart.RadialSchurBlock.sourceComplexRowSchurEnergyDensity_nonneg
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
open Ehrhart.RadialSchurBlock
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic EnvelopeGeneralTorusDescent SchurConvexity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

theorem Ehrhart.RadialSchurBlock.sourceComplexRowSchurEnergyDensity_nonneg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) :
    0 ≤ sourceComplexRowSchurEnergyDensity A b := by sorry
