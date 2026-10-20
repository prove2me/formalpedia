-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetFiltration_real_jetLayercake_le_nat_sum
-- name    : Ehrhart.BergmanJetFiltration.real_jetLayercake_le_nat_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/a3dc3f7c-d8d7-4fa3-85bd-ff3f39d35195
-- title:
--   Ehrhart.BergmanJetFiltration.real_jetLayercake_le_nat_sum
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
open Ehrhart.BergmanJetFiltration
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem Ehrhart.BergmanJetFiltration.real_jetLayercake_le_nat_sum (n d N : ℕ) :
    (N : ℝ) * (d : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.range N,
        (d - (n + j).choose n)) : ℕ) := by sorry
