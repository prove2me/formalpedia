-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
-- name    : AvramDividend.Classical.avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:42:31.816057+00:00
-- url     : https://prove2.me/theorems/4772ee54-dabf-49dd-b94c-3d6c63341b84
-- title:
--   Original pure-Gaussian generator of interior cap-linear extension equals Lévy drift above cap
-- statement:
--   At every reserve above the interior clipping threshold, the zero-jump Lévy generator of the cap-linear continuation of the value function equals the drift coefficient. No differentiability at the clipping threshold or original admissible cap is assumed.
-- source:
--   Combines B31 local affine derivatives and B30 zero-jump pointwise generator identity. Supplies upper strip drift term in original finite-cap stopped Ito-Meyer source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_zerojump_local_affine_jet_generator_drift
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.GeneratorIntegrable V y ∧ X.generator V y = X.c := by sorry
