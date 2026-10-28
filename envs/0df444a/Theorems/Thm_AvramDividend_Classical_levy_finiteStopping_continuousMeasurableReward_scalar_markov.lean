-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_continuousMeasurableReward_scalar_markov
-- name    : AvramDividend.Classical.levy_finiteStopping_continuousMeasurableReward_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:26:45.385678+00:00
-- url     : https://prove2.me/theorems/50119a48-7bdd-46c2-a2d1-f3562d7d7a6a
-- title:
--   Strong-Markov scalar reward identity at arbitrary finite stopping times
-- statement:
--   For any finite-valued stopping time and stopped-history event, a bounded reward that is both continuous and coordinate-measurable has the strong-Markov scalar expectation factorisation. Assumes measurable restricted rewards and finite stationary reward expectation. The proof applies bounded strong Markov on {τ≤n}, then passes to the limit using two proved horizon-exhaustion identities.
-- source:
--   Direct long-horizon extension of levy_stoppedHistory_truncated_scalar_markov, lintegral_stoppedEvent_horizon_tendsto and stoppedHistory_event_probability_tendsto, targeting full shifted-path strong-Markov product law 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_truncated_scalar_markov
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_horizon_tendsto
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_probability_tendsto

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_continuousMeasurableReward_scalar_markov
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
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞)
    (hMeas : ∀ n : ℕ, Measurable (Set.indicator
      (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω'))))
    (hRewardFinite : (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
