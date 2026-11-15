-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
-- name    : AvramDividend.Classical.avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:42:32.920582+00:00
-- url     : https://prove2.me/theorems/439e6e22-b71b-4cef-b308-25c5cb6db1e5
-- title:
--   Original pure-Gaussian generator of interior cap-linear continuation equals original generator below clipping level
-- statement:
--   Below the interior cap-linear clipping threshold, the clipped value agrees locally with the original value. In the zero-jump case, the Gaussian generator inherits the original generator there. This transfers the HJB inequality on the original smooth interior reserve band to the clipped test function, without requiring smoothness at the clipping threshold.
-- source:
--   B33 locality of zero-jump generator and neighbourhood equality below b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB33_zerojump_generator_of_germs_equal
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b y : ℝ) (hy : y < b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.generator V y = X.generator w y := by sorry
