-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
-- name    : AvramDividend.Classical.avram_a19_affine_singular_subunit_original_generator_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:14:00.574216+00:00
-- url     : https://prove2.me/theorems/24cc445a-f0fa-4a7b-adee-5dd320c77d82
-- title:
--   Original singular Levy generator has explicit compensated affine formula below reserve one
-- statement:
--   For the original bounded-variation Levy generator with the singular negative density, the zero-extended affine candidate has an exact explicit generator formula at each positive subunit reserve. The source Levy measure has no mass on nonnegative jumps, so the integral over negative jumps agrees with the previously proved whole-line compensated integral.
-- source:
--   A19 exact original-generator countermodel; 6ffbc13a original compensated density integral and Avram Levy-measure negative support, 7 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_singular_density_generator_integral
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_subunit_original_generator_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x =
      X.c + (2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1))) := by sorry
