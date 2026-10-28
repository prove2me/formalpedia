-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_path_lintegral_eq_of_equal_triplet_ws01b
-- name    : AvramDividend.Classical.cross_levy_path_lintegral_eq_of_equal_triplet_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:51:24.025827+00:00
-- url     : https://prove2.me/theorems/150b21e0-b4e9-4130-b8e6-83eedfbfe6de
-- title:
--   Path-functional nonnegative expectations agree for equal Lévy triplets
-- statement:
--   If two spectrally negative Lévy processes have identical drift, Gaussian coefficient and Lévy measure, their entire path laws coincide. Consequently every Borel-measurable nonnegative path functional has the same extended nonnegative expectation on either process. This reusable transfer applies to future killed-resolvent payoffs once represented as measurable functions of the complete Lévy path, regardless of underlying probability spaces.
-- source:
--   Canonical Proved path-law theorem AvramDividend.Classical.cross_levy_whole_path_law_of_equal_triplet and Mathlib's lintegral_map.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_path_lintegral_eq_of_equal_triplet_ws01b
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (g : (ℝ≥0 → ℝ) → ENNReal) (hg : Measurable g) :
    (∫⁻ ω : Ω₁, g (fun t : ℝ≥0 => X.X t ω) ∂P₁) =
    (∫⁻ ω : Ω₂, g (fun t : ℝ≥0 => Y.X t ω) ∂P₂) := by sorry
