-- Prove2me | Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_holomorphic_commute
-- name    : Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_holomorphic_commute
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/13ffb920-8f41-46f7-b570-4f919cb0adec
-- title:
--   Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_holomorphic_commute
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

theorem Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_holomorphic_commute {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    barPartialCoordinate
      (fun w => holomorphicCoordinate F w i) z j =
    holomorphicCoordinate
      (fun w => barPartialCoordinate F w j) z i := by sorry
