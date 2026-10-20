-- Prove2me | Theorems.Thm_Ehrhart_TorusWeakDolbeaultMollification_barPartial_complexReal_convolution_eq_of_compact_green
-- name    : Ehrhart.TorusWeakDolbeaultMollification.barPartial_complexReal_convolution_eq_of_compact_green
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/005cd876-3aaf-4252-ba0f-bd35e5f29222
-- title:
--   Ehrhart.TorusWeakDolbeaultMollification.barPartial_complexReal_convolution_eq_of_compact_green
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
open Ehrhart.TorusWeakDolbeaultMollification
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths DolbeaultRegularity DolbeaultGraphDistributionBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusWeakDolbeaultMollification.barPartial_complexReal_convolution_eq_of_compact_green
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {G : Fin n → TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : ∀ (ψ : TorusCharacters.LogSpace n → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ j : Fin n,
        (∫ t : TorusCharacters.LogSpace n,
          g t * coverBarPartialTest ψ j t
          ∂(volume : Measure (TorusCharacters.LogSpace n))) =
        -(2 : ℂ) *
          (∫ t : TorusCharacters.LogSpace n,
            G j t * (ψ t : ℂ)
            ∂(volume : Measure (TorusCharacters.LogSpace n))))
    (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      x j =
    (G j ⋆[complexRealMultiplication,
      (volume : Measure (TorusCharacters.LogSpace n))] κ) x := by sorry
