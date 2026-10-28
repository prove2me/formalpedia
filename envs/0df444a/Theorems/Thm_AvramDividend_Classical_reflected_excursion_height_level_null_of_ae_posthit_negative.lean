-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_posthit_negative
-- name    : AvramDividend.Classical.reflected_excursion_height_level_null_of_ae_posthit_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:13:04.018717+00:00
-- url     : https://prove2.me/theorems/156141cd-ad94-4165-a524-34c159d556c8
-- title:
--   Excursion-height singleton has zero measure if post-hit downward regularity holds almost everywhere under the excursion measure
-- statement:
--   Let n be an arbitrary measure on a space of sample excursions. For a fixed positive or zero level x, suppose excursions of exact height x possess an in-lifetime hitting time T at the level, the reflected regulator S is nondecreasing, and the reflected excursion never exceeds x before lifetime. If under n almost every sample excursion's underlying path has negative increments arbitrarily soon after its hitting time T, then the singleton excursion-height set {H=x} has n-measure zero. The proof uses the canonically established deterministic strict-overshoot lemma to force a contradiction for a.e. such excursion. The essential stochastic obligation of proving the post-hit property under the excursion measure remains separate and is not assumed from ordinary-P strong Markov without justification.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, Section 2.3, excursion height no-atom argument; explicitly separates deterministic pathwise and excursion-measure strong Markov ingredients.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflected_excursion_height_level_null_of_ae_posthit_negative
    {E : Type*} [mE : MeasurableSpace E] (n : Measure E)
    (S Y : E → ℝ≥0 → ℝ)
    (T ζ H : E → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ e : E, H e = x →
      T e < ζ e ∧
      Monotone (S e) ∧
      S e (T e) - Y e (T e) = (x : ℝ) ∧
      ∀ t : ℝ≥0, T e ≤ t → t < ζ e →
        S e t - Y e t ≤ (x : ℝ))
    (hNegAE : ∀ᵐ e ∂n, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        Y e (T e + s) < Y e (T e)) :
    n {e : E | H e = x} = 0 := by sorry
