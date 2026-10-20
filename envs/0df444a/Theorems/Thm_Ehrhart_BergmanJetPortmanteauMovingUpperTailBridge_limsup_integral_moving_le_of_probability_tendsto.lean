-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauMovingUpperTailBridge_limsup_integral_moving_le_of_probability_tendsto
-- name    : Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_integral_moving_le_of_probability_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/a93f6c59-4bf4-4daf-ab26-9953dff10c53
-- title:
--   Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_integral_moving_le_of_probability_tendsto
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

theorem Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.limsup_integral_moving_le_of_probability_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    (f : ℕ → X → ℝ) (g : X → ℝ) (C : ℝ)
    (hfmeas : ∀ k : ℕ, Measurable (f k))
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C)
    (hfnonneg : ∀ (k : ℕ) (x : X), 0 ≤ f k x)
    (hfbound : ∀ (k : ℕ) (x : X), f k x ≤ C)
    (hgnonneg : ∀ x : X, 0 ≤ g x)
    (hgbound : ∀ x : X, g x ≤ C)
    (hjoint : ∀ t : ℝ,
      (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
        {x : X | t ≤ g x}) :
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop ≤
      ∫ x, g x ∂(μ : Measure X) := by sorry
