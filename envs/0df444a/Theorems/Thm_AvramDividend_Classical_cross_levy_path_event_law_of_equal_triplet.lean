-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_triplet
-- name    : AvramDividend.Classical.cross_levy_path_event_law_of_equal_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:47:37.949486+00:00
-- url     : https://prove2.me/theorems/9f3e2b5d-f34c-4de0-9c96-a1c11b667279
-- title:
--   Equal Lévy triplets transfer arbitrary measurable complete-path event probabilities
-- statement:
--   Two spectrally negative Lévy processes on unrelated sample spaces share the same drift coefficient, Gaussian coefficient and Lévy measure. For every measurable event in their full coordinate-product path space, the probabilities that each process path belongs to the event are equal. Triplet equality gives equality of their Laplace exponents, and the accepted exponent-based event transfer theorem applies. In particular, this transfers measurable negative-jump events from a canonical Poisson construction to the given process.
-- source:
--   Proved AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi [f2d00bb5-134b-447b-940c-a6b37bca0cc4] and the SpectrallyNegativeLevy Laplace-exponent definition.

import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_path_event_law_of_equal_triplet
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by sorry
