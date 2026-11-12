-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact
-- name    : AvramDividend.Classical.avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:30:52.6552+00:00
-- url     : https://prove2.me/theorems/0758b960-b589-40a3-81e9-bcea9236219c
-- title:
--   Exact original BV masked physical generator equals drift and jump grids
-- statement:
--   The existing proved BV discounted generator decomposition extends exactly to an arbitrary strict pre-ruin interior cell mask. The finite sum over active cells becomes a filtered sum, allowing its generator and drift parts to cancel in phys85, leaving only the true negative-mark Riemann compensator quadrature.
-- source:
--   Masked sum algebraic bridge for phys85 and Proved phys83 66b79837

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (A : ℕ → Prop) [DecidablePred A]
    (z t a : ℕ → ℝ)
    (hGen : ∀ i, A i → X.GeneratorIntegrable w (z i)) :
    (∑ i ∈ Finset.range n, if A i then
      Real.exp (-(q * t i)) *
        (X.generator w (z i) - q * w (z i)) * a i else 0) =
    (∑ i ∈ Finset.range n, if A i then
      Real.exp (-(q * t i)) *
        (X.drift * deriv w (z i) - q * w (z i)) * a i else 0) +
    (∑ i ∈ Finset.range n, if A i then
      (∫ y in Iio (0 : ℝ), Real.exp (-(q * t i)) *
        (w (z i + y) - w (z i)) ∂X.ν) * a i else 0) := by sorry
