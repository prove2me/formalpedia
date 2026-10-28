-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_generator_and_slope_bounds
-- name    : AvramDividend.Classical.capped_hjb_generator_and_slope_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:51:34.90545+00:00
-- url     : https://prove2.me/theorems/a1eb6049-1573-4041-9cda-9915a302a53c
-- title:
--   HJB maximum condition implies non-positive discounted generator and dividend slope at least one
-- statement:
--   Inside the capped continuation region, the HJB maximum equation yields the generator integrability hypothesis, generator w ≤ q w, and derivative w ≥ 1. These are the two analytic inequalities used separately in the finite-horizon dividend verification, in both bounded- and unbounded-variation cases.
-- source:
--   Exact HJB premise of AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation (e068df0b-1a13-4858-a96e-dd12c65f0983) and unbounded-variation counterpart.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_generator_and_slope_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.GeneratorIntegrable w y ∧
      X.generator w y ≤ q * w y ∧ 1 ≤ deriv w y := by sorry
