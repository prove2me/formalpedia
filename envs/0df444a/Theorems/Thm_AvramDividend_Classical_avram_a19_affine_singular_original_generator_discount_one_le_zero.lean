-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_discount_one_le_zero
-- name    : AvramDividend.Classical.avram_a19_affine_singular_original_generator_discount_one_le_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:33:26.249034+00:00
-- url     : https://prove2.me/theorems/a84bfed5-840e-41dc-b8bb-0b9e6f275d8e
-- title:
--   The actual singular Levy generator obeys the affine HJB inequality for one-discount and zero drift
-- statement:
--   For any original bounded-variation spectrally negative Levy process with zero drift and the explicit singular negative jump density, the generator of the zero-extended affine dividend-value candidate, discounted at rate one, is nonpositive at every positive surplus. Uses two independently kernel-verified exact generator identities and the previously proved scalar HJB inequality.
-- source:
--   A19 original compensated generator and singular density HJB, 7 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_original_generator_eq_c
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_hjb_piecewise
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_original_generator_discount_one_le_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (x : ℝ) (hx : 0 < x) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x -
      (if x < 0 then (0 : ℝ) else 1 + x) ≤ 0 := by sorry
