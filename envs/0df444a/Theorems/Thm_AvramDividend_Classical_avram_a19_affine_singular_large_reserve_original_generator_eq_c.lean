-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_original_generator_eq_c
-- name    : AvramDividend.Classical.avram_a19_affine_singular_large_reserve_original_generator_eq_c
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:59:48.186771+00:00
-- url     : https://prove2.me/theorems/4dda1d17-e4b9-4a44-85cc-e5398ee2b6d5
-- title:
--   Original Levy generator of singular affine candidate equals the drift coefficient above reserve one
-- statement:
--   For a bounded-variation spectrally negative Levy process with the explicit singular negative jump density, the original compensated Levy generator of the zero-extended affine candidate is exactly the process drift coefficient for all reserves at least one. The jump integral is zero on the support of the measure.
-- source:
--   A19 exact original generator first-cell countermodel, using established derivative-one and singular-density support results, 7 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_integrand_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_large_reserve_original_generator_eq_c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 1 ≤ x) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x = X.c := by sorry
