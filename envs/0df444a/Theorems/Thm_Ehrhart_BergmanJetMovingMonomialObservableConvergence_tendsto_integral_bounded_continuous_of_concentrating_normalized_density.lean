-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetMovingMonomialObservableConvergence_tendsto_integral_bounded_continuous_of_concentrating_normalized_density
-- name    : Ehrhart.BergmanJetMovingMonomialObservableConvergence.tendsto_integral_bounded_continuous_of_concentrating_normalized_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/85f27da3-19ea-4377-bd7e-0da70c223142
-- title:
--   Ehrhart.BergmanJetMovingMonomialObservableConvergence.tendsto_integral_bounded_continuous_of_concentrating_normalized_density
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
open Ehrhart.BergmanJetMovingMonomialObservableConvergence
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetMovingMonomialTailConvergence
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetMovingMonomialObservableConvergence.tendsto_integral_bounded_continuous_of_concentrating_normalized_density
    {n : ℕ}
    (w : ℕ → Space n → ℝ)
    (hw : ∀ᶠ k : ℕ in atTop,
      Integrable (w k) (volume : Measure (Space n)))
    (hwnonneg : ∀ k : ℕ, ∀ x : Space n, 0 ≤ w k x)
    (hwmass : ∀ᶠ k : ℕ in atTop,
      (∫ x : Space n, w k x
        ∂(volume : Measure (Space n))) = 1)
    (x₀ : Space n)
    (hwtail : ∀ {r : ℝ}, 0 < r →
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n)))
        atTop (𝓝 (0 : ℝ)))
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : Space n, f x * w k x
          ∂(volume : Measure (Space n)))
      atTop (𝓝 (f x₀)) := by sorry
