-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_futureReward_tonelli
-- name    : AvramDividend.Classical.levy_finiteGrid_stoppedEvent_futureReward_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:19:45.210026+00:00
-- url     : https://prove2.me/theorems/77ea0055-96ae-4f44-9243-9961efd12048
-- title:
--   Finite-grid stopped-event reward integral against the Lévy future-path product law
-- statement:
--   For finitely many deterministic grid times, suppose each stopped-history event A_i is measurable at its grid time and every finite cylinder of future Lévy increments is independent of that time's past filtration. The sum of expected nonnegative functionals of each event indicator and complete future increment path equals the sum of product integrals over the event indicator's law and the future path's law. This supplies an explicit stopped-event interface to the proved arbitrary-history finite-grid Markov–Tonelli formula and is designed to be specialised to the upcrossing-versus-ruin partition.
-- source:
--   Intermediate towards the strong-Markov barrier dividend factorisation, canonical Open child 79978d61-9d1f-4b20-b8a5-114797a8e380 of mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Derived from the proved finite_grid_state_future_lintegral_sum theorem UUID 776eca40-3730-4387-8c4a-0038b8e6d971. No scale function hypotheses.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_grid_state_future_lintegral_sum

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteGrid_stoppedEvent_futureReward_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (hFinite : ∀ i, ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s i + t) ω - X.X (s i) ω) inferInstance)
        (𝓕 (s i)) P)
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
