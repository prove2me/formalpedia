-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound
-- name    : AvramDividend.Classical.avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:48:44.878942+00:00
-- url     : https://prove2.me/theorems/ca56314d-0ab5-44b3-809b-ba7d3fe551e6
-- title:
--   Original localized fixed-level Gaussian occupation product mass decays at inverse mesh refinement
-- statement:
--   For the actual original zero-jump unbounded-variation spectrally negative Lévy source and any adapted monotone dividend strategy, fix a prescribed spatial level, a finite deterministic horizon, and a bound M on total dividend variation. There exists a finite positive constant C independent of the natural mesh refinement m such that the product probability and Lebesgue time measure of original reserve hitting that level on paths with terminal dividend variation at most M is bounded by C/m. This is exactly the substantive fourth-power time-grid and Gaussian anti-concentration estimate; B272 then follows from an inverse-natural squeeze and countable union over M. The original source, dividend, and filtration are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB274_original_localised_fixed_level_product_mass_inverse_grid_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M : ℕ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ m : ℕ,
        (P.prod volume)
          {z : Ω × ℝ |
            0 < z.2 ∧ z.2 < (n : ℝ) ∧
            x + X.X (Real.toNNReal z.2) z.1 -
              rightLimit D (Real.toNNReal z.2) z.1 = b ∧
            D n z.1 - D 0 z.1 ≤ (M : ℝ)} ≤
          (C : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by sorry
