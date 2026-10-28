-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
-- name    : AvramDividend.Classical.cross_levy_whole_path_law_of_equal_marginals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:25:24.228425+00:00
-- url     : https://prove2.me/theorems/99d73ada-1f35-4196-aa9d-fd7b1e29012b
-- title:
--   Spectrally negative Lévy processes with identical one-time marginal laws have equal entire coordinate path laws across different probability spaces
-- statement:
--   For any two spectrally negative Lévy processes X and Y living on arbitrary, unrelated probability spaces, equality of their one-time marginal laws at every nonnegative time implies equality of their complete coordinate-product path probability measures. Prove this by independently recovering joint increment vectors, finite monotone-grid path values, arbitrary finite-coordinate laws using a sorted-grid enumeration, and then applying finite-dimensional cylinder uniqueness. No sample coupling or equality of individual paths is assumed. This is the exact abstract Lévy identification theorem needed to transfer a genuine canonical càdlàg path-law after independently proving matching original and canonical one-time laws.
-- source:
--   Composition of Proved cross_levy_zeroBasedGrid_law_of_marginals [8b70d80d-0845-405c-8907-7af83009e946], published cross_sample_finite_coord_law_of_grid_vector_law [18a3a4d5-5329-448e-994e-429dff038421], proposed finite_time_set_has_monotone_zero_started_grid, and Proved cross_sample_path_law_eq_of_all_finite_vector_laws [89f430bc-6696-4d3e-a36e-c53345c1341d]. Do not publish until all imports Proved.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
import Theorems.Thm_AvramDividend_Classical_cross_sample_finite_coord_law_of_grid_vector_law
import Theorems.Thm_AvramDividend_Classical_finite_time_set_has_monotone_zero_started_grid
import Theorems.Thm_AvramDividend_Classical_cross_levy_zeroBasedGrid_law_of_marginals

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_whole_path_law_of_equal_marginals
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by sorry
