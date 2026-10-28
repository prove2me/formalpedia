-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_negative_on_hitting
-- name    : AvramDividend.Classical.reflected_excursion_height_level_null_of_ae_negative_on_hitting
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:13:03.541197+00:00
-- url     : https://prove2.me/theorems/d3195575-9b7c-4e82-a98b-6bcc18cb4221
-- title:
--   Excursion-height atomlessness from downward regularity conditional on survival to the hitting time
-- statement:
--   For a potentially sigma-finite excursion measure n, assume the excursion strong-Markov output only on the event that the relevant height hitting time T occurs strictly before excursion lifetime ζ: n-almost everywhere on T<ζ, the underlying path has negative increments arbitrarily soon after T. Then every exact positive excursion-height singleton {H=x} has n-measure zero if, on its level event, T reaches the height x, the regulator is monotone and the path stays below x until lifetime. Unlike the stronger earlier conditional lemma this requires no post-hitting law on excursions that never reach the level, exactly matching the excursion measure strong Markov restriction. The stochastic source-law transfer and construction of n remain separate.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, section 2.3 excursion-height no-atom argument, separating stopped-excursion survival event from the pathwise contradiction.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflected_excursion_height_level_null_of_ae_negative_on_hitting
    {E : Type*} [mE : MeasurableSpace E] (n : Measure E)
    (S Y : E → ℝ≥0 → ℝ)
    (T ζ H : E → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ e : E, H e = x →
      T e < ζ e ∧
      Monotone (S e) ∧
      S e (T e) - Y e (T e) = (x : ℝ) ∧
      ∀ t : ℝ≥0, T e ≤ t → t < ζ e →
        S e t - Y e t ≤ (x : ℝ))
    (hNegOnHitAE : ∀ᵐ e ∂n, T e < ζ e →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          Y e (T e + s) < Y e (T e)) :
    n {e : E | H e = x} = 0 := by sorry
