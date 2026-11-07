-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_original_positive_gaussian_compact_C2_discount_envelope
-- name    : AvramDividend.Classical.avram_f16_original_positive_gaussian_compact_C2_discount_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:17:34.377218+00:00
-- url     : https://prove2.me/theorems/c17053bc-e779-4531-a73a-382327a92418
-- title:
--   Original positive Gaussian Lévy compact interior band has simultaneous discounted C² coefficient bounds
-- statement:
--   For the actual original spectrally negative Lévy process with strictly positive Gaussian coefficient, the original interior C² value candidate has jointly bounded discounted first and second derivative coefficients on every compact band inside the admissible surplus domain, uniformly over nonnegative times. Combining the already Proved original compact gradient bound and original sigma²-weighted curvature bound removes the Gaussian scaling by positivity. Supports localising the true stopped gradient and Hessian in the zero-jump Gaussian source branch.
-- source:
--   Source-exact original-process compact envelope; no finite upper cap assumption; requires the actual positive sigma, hq≥0, and interior compact band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f16_original_positive_gaussian_compact_C2_discount_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH) := by sorry
