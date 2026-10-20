-- Prove2me | Theorems.Thm_Ehrhart_JetCounting_card_jetIndexLT
-- name    : Ehrhart.JetCounting.card_jetIndexLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/a94dad62-fa5d-48ee-8275-cfb4d5d00958
-- title:
--   Ehrhart.JetCounting.card_jetIndexLT
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
open Ehrhart.JetCounting
open scoped BigOperators

theorem Ehrhart.JetCounting.card_jetIndexLT (n j : ℕ) (hj : 0 < j) :
    Fintype.card (JetIndexLT n j) = (n + j - 1).choose n := by sorry
