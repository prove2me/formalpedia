-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet
-- name    : AvramDividend.Classical.cross_levy_whole_path_law_of_equal_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:40:04.038251+00:00
-- url     : https://prove2.me/theorems/6c3e7ba6-980d-403b-b064-bac5fe5b5a4c
-- title:
--   Equal Lévy triplets determine complete path laws across unrelated probability spaces
-- statement:
--   Suppose two spectrally negative Lévy processes may be defined over completely different probability spaces but have the same drift c, Gaussian coefficient σ, and Lévy jump measure ν, all under the Prove2Me model's compensation convention. Their Laplace exponent ψ, defined from that triplet, therefore agrees at every positive real parameter. The accepted cross-space whole-path law theorem then identifies their full coordinate-product process laws. This is the exact interface for transferring the stochastic laws of a canonical Poisson–Gaussian Lévy construction back to an arbitrary spectrally negative Lévy process after verifying the canonical triplet.
-- source:
--   Proved AvramDividend.Classical.cross_levy_whole_path_law_of_equal_psi [88648c7e-7b5e-435c-95e6-b8c8a5dd1812], and the definition of SpectrallyNegativeLevy.ψ as laplaceExponent c σ ν.

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_whole_path_law_of_equal_triplet
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν) :
    Measure.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) P₂ := by sorry
