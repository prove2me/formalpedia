-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_strict_tail_real_density
-- name    : AvramDividend.Classical.bv_esscher_canonical_strict_tail_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:11:05.190857+00:00
-- url     : https://prove2.me/theorems/d48c7b7d-446a-449a-8719-1a182f0f3fbe
-- title:
--   Canonical Esscher strict-tail measure has an explicit real Lebesgue density
-- statement:
--   Identify the canonical discounted Lévy strict positive jump-tail measure exactly with the Lebesgue measure weighted by the explicit nonnegative real strict-tail density, zero on nonpositive arguments. Finite discounted first moment follows directly from the already proved bounded-variation positive Esscher-root estimate.
-- source:
--   Accepted proof of bv_esscher_positive_tail_kernel_shape_of_root (61873c37-24a7-40f2-aea1-1625a1e7ce12) combined with proved positive_strict_tail_measure_real_density (24870e2e-dfa1-4622-bed6-ec0bd7e0a56e).

import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_measure_real_density
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_strict_tail_real_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
      ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}) =
    volume.withDensity (fun t : ℝ =>
      ENNReal.ofReal (if 0 < t then
        (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}).toReal else 0)) := by sorry
