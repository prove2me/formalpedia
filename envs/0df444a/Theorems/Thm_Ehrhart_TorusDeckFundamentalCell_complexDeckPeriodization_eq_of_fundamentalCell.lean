-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckFundamentalCell_complexDeckPeriodization_eq_of_fundamentalCell
-- name    : Ehrhart.TorusDeckFundamentalCell.complexDeckPeriodization_eq_of_fundamentalCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/82af3a77-c3ca-4880-b79a-ca7c797103b7
-- title:
--   Ehrhart.TorusDeckFundamentalCell.complexDeckPeriodization_eq_of_fundamentalCell
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
open Ehrhart.TorusDeckFundamentalCell
open Set Function Filter MeasureTheory Matrix
open WeightedTorusDistributionBridge TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusDeckFundamentalCell.complexDeckPeriodization_eq_of_fundamentalCell
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hcell : tsupport ψ ⊆
      {z : TorusCharacters.LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b})
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b) :
    complexDeckPeriodization ψ
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      ψ (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) := by sorry
