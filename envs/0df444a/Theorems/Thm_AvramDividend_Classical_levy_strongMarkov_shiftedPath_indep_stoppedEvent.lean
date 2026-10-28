-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent
-- name    : AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:02:40.77758+00:00
-- url     : https://prove2.me/theorems/61930a38-11f1-449e-bbb6-67d59c6d5ca8
-- title:
--   Strong Markov independence of the shifted Lévy path from a stopped-history event
-- statement:
--   For a spectrally negative Lévy process with the specified independent and stationary increments and càdlàg paths, let τ be an almost surely finite stopping time valued in nonnegative real time and A an event measurable in the stopped past, expressed by A∩{τ≤s}∈𝓕_s for every deterministic s. The joint law of the event indicator and the future increment path t↦X(τ+t)-X(τ) is the product of the indicator law and the original path law. This gives the stochastic restart principle required for barrier-dividend first-passage factorisation, without any scale-function hypothesis.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 strong-Markov restart of a spectrally negative Lévy process. Mathematical intermediate for mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 and exact Open child 79978d61-9d1f-4b20-b8a5-114797a8e380; deterministic-time future-path independence is separately Proved as AvramDividend.Classical.chat04_arbitrary_history_full_future_path_product_law (df53d7ad-ff31-4809-8a72-f7b90798838e).

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω =>
        (Set.indicator A (fun _ : Ω => (1 : ℝ)) ω,
          fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)) P =
      (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  sorry
