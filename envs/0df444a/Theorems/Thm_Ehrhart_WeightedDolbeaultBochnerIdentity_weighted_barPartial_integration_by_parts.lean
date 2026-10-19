-- Prove2me | Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_barPartial_integration_by_parts
-- name    : Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_barPartial_integration_by_parts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/e61df08a-5703-49fe-bd30-ad58e24c4751
-- title:
--   Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_barPartial_integration_by_parts
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
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate

theorem Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_barPartial_integration_by_parts
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate F z j * G z
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * weightedAntiholomorphicDerivative a G j z
      ∂(coverWeightedMeasure a)) := by sorry
