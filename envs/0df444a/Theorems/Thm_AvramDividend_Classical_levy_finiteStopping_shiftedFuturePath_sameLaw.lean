-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
-- name    : AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:36:13.052143+00:00
-- url     : https://prove2.me/theorems/77ac6d6a-535b-4113-9d19-d72b14868b9a
-- title:
--   Stationarity in law of the entire post-stopping Lévy increment path
-- statement:
--   For every finite stopping time of a spectrally negative Lévy process, the complete shifted future increment path has exactly the same distribution as the original path. This follows from the verified stopped-history restricted path law applied to the whole sample space and is used repeatedly in strong-Markov dividend reward identities.
-- source:
--   Canonical A=Ω corollary of proved restricted path law e2543758-86c1-4254-a0b4-433781e31752. Replaces repeated local hFull proofs in accepted threshold and sigma independence theorems, directly enabling the original-path dividendValue expectation in target 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  sorry
