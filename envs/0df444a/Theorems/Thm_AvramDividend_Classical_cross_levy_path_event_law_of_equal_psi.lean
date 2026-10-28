-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:01:18.709982+00:00
-- url     : https://prove2.me/theorems/f2d00bb5-134b-447b-940c-a6b37bca0cc4
-- title:
--   Equal Lévy Laplace exponents transfer probabilities of all measurable path events
-- statement:
--   Given two spectrally negative Lévy processes on arbitrary sample spaces and equal real Laplace exponents at every positive parameter, any measurable event in their common path coordinate space has identical probability under both processes. One-time marginal uniqueness from the exponent and the Proved Lévy finite-dimensional path-law theorem identify their pushed-forward path measures; two applications of Measure.map_apply transfer an event's probability. This theorem is the direct interface from a canonical Poisson jump construction, once its Lévy Laplace exponent and a measurable jump-count event are established.
-- source:
--   Proved cross_levy_marginal_laws_of_equal_psi [22d0e193-bcb9-462b-b8f8-48fdde83367b], Proved cross_levy_whole_path_law_of_equal_marginals [99d73ada-1f35-4196-aa9d-fd7b1e29012b], pinned Mathlib Measure.map_apply.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by sorry
