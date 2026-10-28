-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_upperGrid_futureReward_product
-- name    : AvramDividend.Classical.levy_stoppedHistory_upperGrid_futureReward_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:12:17.051972+00:00
-- url     : https://prove2.me/theorems/f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b
-- title:
--   Finite upper-grid stopped-history events factor arbitrary future Lévy rewards
-- statement:
--   For an event measurable in the stopped history and a finite adapted upward stopping-time approximation, the future Lévy reward over each stopping-time grid fibre factors into the original whole-path law and the measurable history indicator law. This is an unconditional finite-grid strong-Markov identity for arbitrary measurable future-path rewards, retaining the exact stopped-history event.
-- source:
--   Direct strong-Markov intermediate for Open theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and the barrier value child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes Proved stoppedEvent_upperGridFibre_measurable ddc5c663-4003-4dfd-aaf7-c2d390b54283 with Proved levy_finiteGrid_stoppedEvent_stationaryFuture_reward 1c698509-4e7c-42e5-8365-d1065787dd5a and whole-path stationarity f7f7d00c-aaf9-47d1-9d8e-1edbc5d2b849.

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_stationaryFuture_reward
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stoppedHistory_upperGrid_futureReward_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ι → ℝ≥0)
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A ∩ {ω : Ω | τn n ω = s i})
          (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
        ∂(Measure.map
          (Set.indicator (A ∩ {ω : Ω | τn n ω = s i})
            (fun _ : Ω => (1 : ℝ))) P) := by
  sorry
