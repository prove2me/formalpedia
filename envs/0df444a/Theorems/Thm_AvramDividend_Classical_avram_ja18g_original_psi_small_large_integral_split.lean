-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_psi_small_large_integral_split
-- name    : AvramDividend.Classical.avram_ja18g_original_psi_small_large_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:54:07.376413+00:00
-- url     : https://prove2.me/theorems/7abcd634-5a47-4c34-b0f3-8e0cc530ebb0
-- title:
--   Original Lévy-Khintchine exponent split into compensated small and large negative bands
-- statement:
--   For θ≥0, partition Iio 0 at -1 in the original Lévy measure, simplifying the indicator in laplaceExponent. The resulting exact identity isolates Gaussian, small compensated jump and large negative jump terms. Supply the original integrability of each band from Standing and the Lévy measure square condition, then restrict-integral additivity.
-- source:
--   J-A18 original exponent algebraic integral decomposition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_psi_small_large_integral_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ z in Ioo (-1 : ℝ) 0,
        Real.exp (θ * z) - 1 - θ * z ∂X.ν) +
      (∫ z in Iic (-1 : ℝ), Real.exp (θ * z) - 1 ∂X.ν) := by sorry
