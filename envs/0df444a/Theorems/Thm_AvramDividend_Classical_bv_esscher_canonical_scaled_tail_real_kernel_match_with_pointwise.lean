-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
-- name    : AvramDividend.Classical.bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:27:15.075265+00:00
-- url     : https://prove2.me/theorems/e07a666f-b6a1-4c8a-9c0a-228ca9232cb3
-- title:
--   Explicit pointwise identification of the canonical BV Esscher tail renewal kernel
-- statement:
--   Under standing bounded-variation assumptions, identify the positive subunit renewal kernel pointwise as the drift-normalised Esscher-weighted strict tail of the negative jump measure, retaining the existing measure equality, continuity, integrability and subunit-mass properties. The accepted predecessor proof already constructs the pointwise identity as hkdef and does not otherwise need changes.
-- source:
--   Source-derived strengthening of accepted bv_esscher_canonical_scaled_tail_real_kernel_match; accepted proof source SHA-256 42c1f7e06da43a5ede2296f653b8503cd4fa2f08306c30bda37e789a2b05c3a3. The existing hkdef witness is now included in the conclusion.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_scaled_drift_real_density
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (k : ℝ → ℝ) (ρ : ℝ),
      (∀ t : ℝ, k t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn k (Ioi (0 : ℝ)) ∧
      AntitoneOn k (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → k t = 0) ∧
      (∀ t : ℝ, 0 ≤ k t) ∧
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ ∧
      (ENNReal.ofReal X.drift)⁻¹ •
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) =
        (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (k t)) := by sorry
