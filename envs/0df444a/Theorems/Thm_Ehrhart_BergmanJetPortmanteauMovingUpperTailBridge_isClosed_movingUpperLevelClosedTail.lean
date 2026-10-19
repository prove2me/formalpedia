-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_isClosed_movingUpperLevelClosedTail
-- name    : Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.isClosed_movingUpperLevelClosedTail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/850853a0-f3fe-4e72-a1e7-048696d47b88
-- title:
--   Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.isClosed_movingUpperLevelClosedTail
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

theorem Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.isClosed_movingUpperLevelClosedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ) (N : ℕ) :
    IsClosed (movingUpperLevelClosedTail f t N) := by sorry
