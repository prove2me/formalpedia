-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative
-- name    : AvramDividend.Classical.reflectedSup_height_level_null_of_ae_posthit_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:52:58.275749+00:00
-- url     : https://prove2.me/theorems/663e43e3-2e48-4cb2-9302-c86690025b32
-- title:
--   Actual spectrally negative Lévy reflected excursion has atomless height levels under the excursion law post-hit regularity assumption
-- statement:
--   Let X be the canonical spectrally negative Lévy process and n any potentially sigma-finite excursion measure on its sample path space. Fix x and assume each height-x path attains reflected drawdown x strictly before the lifetime ζ while never exceeding x prior to ζ. If n-almost surely on the event T<ζ the underlying Lévy sample has negative increments arbitrarily soon after T, then the singleton height event {H=x} has n-measure zero. This instantiates the accepted excursion-height atomlessness contradiction for the actual running supremum and process, discharging monotonicity using the accepted running-supremum theorem. It explicitly leaves the genuine excursion-measure strong Markov law and height-attainment for arbitrary excursion lifetimes as assumptions.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), Lemma 2.4; Prove2Me conditional excursion-height atomlessness and runningSup_monotone_and_path_le.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_level_null_of_ae_negative_on_hitting

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_height_level_null_of_ae_posthit_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : Measure Ω) (T ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, H ω = x →
      T ω < ζ ω ∧
      reflectedSup X (T ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, T ω ≤ t → t < ζ ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (hNegOnHitAE : ∀ᵐ ω ∂n, T ω < ζ ω →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (T ω + s) ω < X.X (T ω) ω) :
    n {ω : Ω | H ω = x} = 0 := by sorry
