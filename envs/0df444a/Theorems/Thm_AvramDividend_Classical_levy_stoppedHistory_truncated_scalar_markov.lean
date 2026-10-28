-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_truncated_scalar_markov
-- name    : AvramDividend.Classical.levy_stoppedHistory_truncated_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:18:39.408208+00:00
-- url     : https://prove2.me/theorems/51076c32-0ba0-41ce-816e-f3cd899ecf77
-- title:
--   Localised strong Markov scalar reward identity on finite-horizon stopped events
-- statement:
--   For any nonnegative real-valued stopping time, the future-path reward on the stopped-history event A restricted to τ≤T factors into the event probability and the original Lévy path reward expectation. Apply bounded strong Markov to min(τ,T), observing it agrees with τ on the restricted event and stopped-history measurability is preserved.
-- source:
--   Direct localisation of verified bounded strong-Markov scalar formula using stoppedHistory_event_min_const. Enables convergence as T→∞ via lintegral_stoppedEvent_horizon_tendsto; no W or scale-function hypotheses. Consumed on route to dividendValue_barrierStrategy_upExit_split_of_standing 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_min_const
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_continuousMeasurableReward_scalar_markov

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stoppedHistory_truncated_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator (A ∩ {ω' : Ω | τ ω' ≤ T})
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P (A ∩ {ω' : Ω | τ ω' ≤ T}) *
      (∫⁻ y, g y ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
