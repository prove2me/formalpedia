-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_grid_limsup_event_law_of_equal_triplet
-- name    : AvramDividend.Classical.cross_levy_grid_limsup_event_law_of_equal_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:12:08.510336+00:00
-- url     : https://prove2.me/theorems/dd87bdde-fee2-414c-a7bb-994c3d43d32c
-- title:
--   Lévy triplet equality transfers infinite downward-grid increment events across path spaces
-- statement:
--   For two spectrally negative Lévy processes with equal drift, Gaussian and jump-measure characteristics, the probability of observing a decrement beyond any threshold on infinitely many finite grids is the same. The event is measurable in the full product path space by the published countable-grid measurability lemma, so it is transferred by the established equality of Lévy path laws. This is the probability-level bridge for pathwise reconstruction of negative Poisson jumps.
-- source:
--   Use the accepted cross_levy_path_event_law_of_equal_triplet with accepted downward_grid_limsup_event_measurable.

import Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_event_measurable
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_triplet

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_grid_limsup_event_law_of_equal_triplet
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a})} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a})} := by sorry
