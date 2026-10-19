-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauUpperTailBridge_integrable_upperSemicontinuous_of_probability_bound
-- name    : Ehrhart.BergmanJetPortmanteauUpperTailBridge.integrable_upperSemicontinuous_of_probability_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/ad66b4f4-ed38-4d14-97a2-59ed5eca99da
-- title:
--   Ehrhart.BergmanJetPortmanteauUpperTailBridge.integrable_upperSemicontinuous_of_probability_bound
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
open Ehrhart.BergmanJetPortmanteauUpperTailBridge
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauUpperTailBridge.integrable_upperSemicontinuous_of_probability_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (μ : ProbabilityMeasure X) {g : X → ℝ} {C : ℝ}
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C) (hnonneg : ∀ x : X, 0 ≤ g x)
    (hbound : ∀ x : X, g x ≤ C) :
    Integrable g (μ : Measure X) := by sorry
