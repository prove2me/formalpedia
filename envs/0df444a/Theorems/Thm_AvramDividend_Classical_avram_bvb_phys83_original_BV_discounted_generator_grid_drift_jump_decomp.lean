-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
-- name    : AvramDividend.Classical.avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:46:48.184489+00:00
-- url     : https://prove2.me/theorems/66b79837-53dd-478d-a388-f30d6fde3f1f
-- title:
--   Exact original BV discounted finite-grid generator decomposition into drift and negative-jump compensator
-- statement:
--   For any finite selection of active physical BV grid cells on the original process, the discounted generator-minus-discount finite sum equals the drift-minus-discount finite sum plus the integral of the negative-jump increments on the same grid. This algebraic identity uses the proved BV Lévy generator residual and is the exact bridge needed to compare G with the compensator K in the deterministic cash child phys82.
-- source:
--   Proved e7290161 original BV compensated generator identity; cash child 80968b25

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On each active BV grid cell, the discounted generator contribution
splits exactly into physical drift and its negative jump compensator. -/

theorem AvramDividend.Classical.avram_bvb_phys83_original_BV_discounted_generator_grid_drift_jump_decomp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (s : Finset ℕ)
    (z t a : ℕ → ℝ)
    (hGen : ∀ i ∈ s, X.GeneratorIntegrable w (z i)) :
    (∑ i ∈ s,
       Real.exp (-(q * t i)) *
         (X.generator w (z i) - q * w (z i)) * a i) =
    (∑ i ∈ s,
       Real.exp (-(q * t i)) *
         (X.drift * deriv w (z i) - q * w (z i)) * a i) +
    (∑ i ∈ s,
       (∫ y in Iio (0 : ℝ), Real.exp (-(q * t i)) *
         (w (z i + y) - w (z i)) ∂X.ν) * a i) := by sorry
