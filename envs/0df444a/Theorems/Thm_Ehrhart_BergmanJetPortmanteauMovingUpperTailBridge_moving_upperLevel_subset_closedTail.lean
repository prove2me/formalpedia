-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_moving_upperLevel_subset_closedTail
-- name    : Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.moving_upperLevel_subset_closedTail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/652decc1-d005-4b5e-a549-da41d7015acd
-- title:
--   Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.moving_upperLevel_subset_closedTail
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
open Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
open Set Function Filter MeasureTheory
open BergmanJetPortmanteauSlopeBridge BergmanJetPortmanteauUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.moving_upperLevel_subset_closedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ)
    {N k : ℕ} (hk : N ≤ k) :
    {x : X | t ≤ f k x} ⊆ movingUpperLevelClosedTail f t N := by sorry
