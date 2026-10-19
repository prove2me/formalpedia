-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
-- name    : Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/247df64e-6c64-4efc-9d66-a2415bdc7de7
-- title:
--   Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
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

theorem Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hjoint : ∀ (x : X) (t : ℝ), g x < t →
      ∃ (N : ℕ) (U : Set X), IsOpen U ∧ x ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U, f k y < t)
    (t : ℝ) :
    (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
      {x : X | t ≤ g x} := by sorry
