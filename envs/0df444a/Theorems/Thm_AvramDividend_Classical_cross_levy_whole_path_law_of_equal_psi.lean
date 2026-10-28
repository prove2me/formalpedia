-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_whole_path_law_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:58:23.842031+00:00
-- url     : https://prove2.me/theorems/88648c7e-7b5e-435c-95e6-b8c8a5dd1812
-- title:
--   Identical positive Lévy Laplace exponents give identical entire path laws across sample spaces
-- statement:
--   Let two spectrally negative Lévy processes be defined over unrelated probability spaces. If their real Laplace exponents coincide for every strictly positive parameter, then their pushforward probability laws on the complete space of real-valued nonnegative-time paths coincide. The accepted positive-MGF uniqueness theorem first identifies all one-time marginal distributions, then the accepted cross-space Lévy whole-path law theorem lifts equality of marginals to full law equality. This is the final law-identification interface before transferring measurable jump-count events from a canonical Poisson construction.
-- source:
--   Composes Proved cross_levy_marginal_laws_of_equal_psi [22d0e193-bcb9-462b-b8f8-48fdde83367b] (accepted candidate 16508) with Proved cross_levy_whole_path_law_of_equal_marginals [99d73ada-1f35-4196-aa9d-fd7b1e29012b] (accepted candidate 16473).

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_whole_path_law_of_equal_psi
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by sorry
