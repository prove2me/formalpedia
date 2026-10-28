-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_continuousCylinderReward_scalar_markov
-- name    : AvramDividend.Classical.levy_boundedStopping_continuousCylinderReward_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:36:53.127012+00:00
-- url     : https://prove2.me/theorems/95e70da4-0a31-479a-a2e9-8f876cb9c67d
-- title:
--   Finite-dimensional continuous cylinder rewards satisfy stopped Lévy strong Markov
-- statement:
--   For any finite collection of future observation times J and any bounded continuous measurable reward of the corresponding Lévy increment vector, its expectation on a bounded stopped-history event factors into that event's mass and the stationary future-path law. This is a concrete finite-dimensional test-function route to the full shifted-path product measure law.
-- source:
--   Finite-cylinder reduction of Proved bounded stopping-time strong-Markov scalar lemma 8d0c23a1-5f8d-4adc-b41f-f7b572a6d3b1; step towards path-law independence 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free dividend split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_continuousMeasurableReward_scalar_markov

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_continuousCylinderReward_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτLE : ∀ ω, τ ω ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0)
    (h : (J → ℝ) → ℝ≥0∞)
    (hh : Continuous h) (hhm : Measurable h)
    (C : ℝ≥0∞) (hbound : ∀ z, h z ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => h (fun j : J =>
        X.X (τ ω' + (j : ℝ≥0)) ω' - X.X (τ ω') ω')) ω ∂P) =
      P A * (∫⁻ y, h (fun j : J => y (j : ℝ≥0))
        ∂(Measure.map
          (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
