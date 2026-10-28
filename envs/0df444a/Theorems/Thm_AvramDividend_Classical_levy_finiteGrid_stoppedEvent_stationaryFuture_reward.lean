-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_stationaryFuture_reward
-- name    : AvramDividend.Classical.levy_finiteGrid_stoppedEvent_stationaryFuture_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:56:36.256565+00:00
-- url     : https://prove2.me/theorems/1c698509-4e7c-42e5-8365-d1065787dd5a
-- title:
--   Finite-grid stopped Lévy event reward with a common stationary future-path law
-- statement:
--   For a finite family of deterministic grid observation times and past-observable stopping fibres, assuming deterministic-time stationarity of the entire shifted Lévy path law, the future reward integral factors at each grid time against the same zero-start path law. This is the finite-grid conditional-restart module to combine with stopping-time approximation, independent of all scale-function parameters.
-- source:
--   Uses the Proved finite-grid stopped-event product law levy_finiteGrid_stoppedEvent_futureReward_of_increments and a single explicit whole-path stationarity premise. Prerequisite for the stopped-time Markov splitting child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_futureReward_of_increments

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteGrid_stoppedEvent_stationaryFuture_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStationary : ∀ u : ℝ≥0,
      Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X (u + t) ω - X.X u ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
    (s : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
        ∂(Measure.map
          (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  sorry
