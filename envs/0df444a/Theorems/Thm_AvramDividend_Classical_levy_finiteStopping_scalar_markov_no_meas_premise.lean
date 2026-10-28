-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_scalar_markov_no_meas_premise
-- name    : AvramDividend.Classical.levy_finiteStopping_scalar_markov_no_meas_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:14:25.880992+00:00
-- url     : https://prove2.me/theorems/1f9015ed-415d-4621-808d-c7d9bc8fe399
-- title:
--   Finite stopping-time Lévy strong Markov with no stopped-reward measurability assumption
-- statement:
--   The expected bounded continuous and product-measurable nonnegative reward of the Lévy future increment path, restricted to a stopped-history event, factors exactly into the event probability and the original-path reward expectation at any finite stopping time. All stopped-reward measurability is derived internally using bounded truncations and adapted grids.
-- source:
--   Uses Proved bounded stopped-future reward measurability and existing canonical finite stopping scalar theorem. Strengthens the strong Markov input to Open stopped-path law 61930a38-11f1-449e-bbb6-67d59c6d5ca8, needed for barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_min_const
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFutureReward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_boundedReward_scalar_markov

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_scalar_markov_no_meas_premise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
