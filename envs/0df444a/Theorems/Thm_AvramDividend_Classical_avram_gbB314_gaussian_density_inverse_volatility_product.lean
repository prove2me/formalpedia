-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB314_gaussian_density_inverse_volatility_product
-- name    : AvramDividend.Classical.avram_gbB314_gaussian_density_inverse_volatility_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:53:50.464817+00:00
-- url     : https://prove2.me/theorems/74c26445-e9b3-4e4b-9654-083c2b8f9daf
-- title:
--   Gaussian reciprocal normalisation and reciprocal volatility multiply to the combined reciprocal coefficient
-- statement:
--   For arbitrary real volatility and an arbitrary real factor, multiplication by the reciprocal Gaussian normalising square root and reciprocal volatility agrees exactly with multiplication by the reciprocal of their product. This is pure commutative inverse multiplication algebra and supplies the final normalisation identity for the original-source B311 Gaussian physical-time kernel factorisation.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB314_gaussian_density_inverse_volatility_product (sigma y : ℝ) :
    (Real.sqrt (2 * Real.pi))⁻¹ * sigma⁻¹ * y =
      (1 / (sigma * Real.sqrt (2 * Real.pi))) * y := by sorry
