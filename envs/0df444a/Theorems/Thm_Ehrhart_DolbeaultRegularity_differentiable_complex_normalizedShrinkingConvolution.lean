-- Prove2me | Theorems.Thm_Ehrhart_DolbeaultRegularity_differentiable_complex_normalizedShrinkingConvolution
-- name    : Ehrhart.DolbeaultRegularity.differentiable_complex_normalizedShrinkingConvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/89fa1c01-9432-451d-ae0f-a95b3cafbefe
-- title:
--   Ehrhart.DolbeaultRegularity.differentiable_complex_normalizedShrinkingConvolution
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
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

theorem Ehrhart.DolbeaultRegularity.differentiable_complex_normalizedShrinkingConvolution
    {n : ℕ} {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0)) (k : ℕ) :
    Differentiable ℂ
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (TorusCharacters.LogSpace n))
       ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
         (volume : Measure (TorusCharacters.LogSpace n))] g) := by sorry
