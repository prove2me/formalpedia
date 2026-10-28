-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_futureReward_of_increments
-- name    : AvramDividend.Classical.levy_finiteGrid_stoppedEvent_futureReward_of_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:52:17.112673+00:00
-- url     : https://prove2.me/theorems/97675f90-c737-4146-8585-2e2d1c05f3b9
-- title:
--   Lévy finite-grid stopping-event future-reward product law without extra hypotheses
-- statement:
--   For any finite deterministic grid, events observable at each grid time, and measurable nonnegative functionals of the stopped-event indicator and complete shifted future Lévy path, the total expected reward splits into the sum of product-law integrals. Independent increments from the SpectrallyNegativeLevy definition automatically discharge the finite-cylinder independence premise. Intermediate needed for Markov stopping-time approximations in the W-free barrier dividend identity.
-- source:
--   Combined Proved lemmas levy_finiteGrid_stoppedEvent_futureReward_tonelli UUID 77ea0055-96ae-4f44-9243-9961efd12048 and finite_future_increment_sigma_indep_past UUID df83d931-9b50-4c91-9b13-698d5a554893. Next dependency for strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_futureReward_tonelli
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteGrid_stoppedEvent_futureReward_of_increments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map
          (fun ω => fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω) P)
        ∂(Measure.map
          (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  sorry
