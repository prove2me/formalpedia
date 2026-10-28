-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_killed_excursion_markov
-- name    : AvramDividend.Classical.reflectedSup_height_level_null_of_killed_excursion_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:42.073185+00:00
-- url     : https://prove2.me/theorems/ef2fced0-b837-4f4e-857a-532a3a532220
-- title:
--   Actual reflected Lévy excursion height is atomless under the exact killed strong-Markov bad-event law and negative regularity of the posthit path law
-- statement:
--   For the actual reflected spectrally negative Lévy process R_t=sup_{s≤t}X_s−X_t, suppose n is a potential sigma-finite excursion law, Q a posthitting Lévy increment path law, T a level-hitting time and ζ the excursion lifetime. If exact height-x excursions reach x at T before ζ and are bounded above by x until their lifetime, Q-almost every path visits negative values arbitrarily soon, and n satisfies the killed strong Markov identity n(T<ζ,bad increment path)=n(T<ζ)Q(bad), then n(H=x)=0. This is a source-faithful actual-process instantiation of the previously proven abstract killed-Markov excursion-height theorem. The genuine n-Markov identity and the true path regularity of Q remain explicit assumptions.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), §2.3 Lemma 2.4; accepted Prove2Me excursion_height_level_null_of_markov_bad_event.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_excursion_height_level_null_of_markov_bad_event

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_height_level_null_of_killed_excursion_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : Measure Ω) (Q : Measure (ℝ≥0 → ℝ))
    (T ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, H ω = x →
      T ω < ζ ω ∧
      reflectedSup X (T ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, T ω ≤ t → t < ζ ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (hRegQ : ∀ᵐ f ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0)
    (hKilledMarkov :
      n {ω : Ω | T ω < ζ ω ∧
        ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧
            X.X (T ω + s) ω - X.X (T ω) ω < 0} =
      n {ω : Ω | T ω < ζ ω} *
        Q {f : ℝ≥0 → ℝ | ¬ ∀ ε : ℝ≥0, 0 < ε →
          ∃ s : ℝ≥0, s < ε ∧ f s < 0}) :
    n {ω : Ω | H ω = x} = 0 := by sorry
