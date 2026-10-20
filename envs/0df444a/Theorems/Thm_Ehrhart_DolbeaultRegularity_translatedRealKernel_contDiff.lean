-- Prove2me | Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_contDiff
-- name    : Ehrhart.DolbeaultRegularity.translatedRealKernel_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:49.881935+00:00
-- url     : https://prove2.me/theorems/59c4ae4e-d08c-4fa8-850d-5aa7a08e55fb
-- title:
--   Ehrhart.DolbeaultRegularity.translatedRealKernel_contDiff
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

theorem Ehrhart.DolbeaultRegularity.translatedRealKernel_contDiff {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : ContDiff ℝ 1 κ)
    (x : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun t : TorusCharacters.LogSpace n => κ (x - t)) := by sorry
