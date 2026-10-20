-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckFullCellDerivative_barPartial_complexDeckPeriodization_eq_on_fundamentalCell
-- name    : Ehrhart.TorusDeckFullCellDerivative.barPartial_complexDeckPeriodization_eq_on_fundamentalCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/82c717c0-f6a1-442e-966c-0a3f34c1c358
-- title:
--   Ehrhart.TorusDeckFullCellDerivative.barPartial_complexDeckPeriodization_eq_on_fundamentalCell
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
open Ehrhart.TorusDeckFullCellDerivative
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge TorusDeckPeriodization TorusDeckFundamentalCell
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff

theorem Ehrhart.TorusDeckFullCellDerivative.barPartial_complexDeckPeriodization_eq_on_fundamentalCell
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b)
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b)
    (j : Fin n) :
    barPartialCoordinate (complexDeckPeriodization ψ)
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) j =
      barPartialCoordinate ψ
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t) j := by sorry
