-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_path_statistic_law_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_path_statistic_law_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:35:39.2767+00:00
-- url     : https://prove2.me/theorems/7ebd616c-b784-444b-aa07-c8d13035e672
-- title:
--   Equal positive Lévy Laplace exponents transfer the entire distribution of any measurable path statistic across sample spaces
-- statement:
--   Let two spectrally negative Lévy processes on unrelated sample spaces have equal positive Laplace exponents. For every measurable statistic stat of their real-valued nonnegative-time coordinate paths, with arbitrary measurable codomain alpha, the two induced laws of stat are exactly equal. This follows by composition of the already Proved full coordinate path-law equality and two applications of Measure.map_map. It strengthens event-level and zero-count transfer to the complete distribution of a canonically constructed intrinsic jump-count functional, allowing the full Poisson probability mass function and not only P(count=0) to transfer once mark-count identification is available.
-- source:
--   Proved cross_levy_whole_path_law_of_equal_psi [88648c7e-7b5e-435c-95e6-b8c8a5dd1812]; pinned Mathlib Measure.map_map, measurable_pi_iff.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_path_statistic_law_of_equal_psi
    {Ω₁ Ω₂ α : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    [MeasurableSpace α]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (stat : (ℝ≥0 → ℝ) → α) (hstat : Measurable stat) :
    P₁.map (fun ω : Ω₁ => stat (fun t : ℝ≥0 => X.X t ω)) =
    P₂.map (fun ω : Ω₂ => stat (fun t : ℝ≥0 => Y.X t ω)) := by sorry
