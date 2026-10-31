-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_weighted_integrated_positive_tail_bound
-- name    : AvramDividend.Classical.avram_wave3_05_tent_weighted_integrated_positive_tail_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:52:10.623376+00:00
-- url     : https://prove2.me/theorems/95a39837-be2b-4092-80a0-553620e77544
-- title:
--   Uniform quadratic weighted L1 bound for the interior compensated Taylor remainder
-- statement:
--   For nonnegative r and θ, if exp(-θu)|F(u)| is globally integrable and the original and weighted triangular interval integrals are locally integrable for x>r, then the exponentially weighted state-integrated absolute Taylor remainder over x>r is bounded by (r²/2) times the global weighted L1 mass of F. This is the interior Gaussian compensated small-jump absolute-product estimate.
-- source:
--   Pinned exact Mathlib, remote private elaboration 30 October 2026; Gaussian source Taylor and weighted W'' depend on this bound.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_weighted_integrated_positive_tail_bound
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hF : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume)
    (hI : ∀ x ∈ Ioi r,
      IntervalIntegrable (fun s : ℝ => (r - s) * F (x - s)) volume 0 r)
    (hJ : ∀ x ∈ Ioi r,
      IntervalIntegrable
        (fun s : ℝ => (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
        volume 0 r)
    (hR : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|)
      (Ioi r) volume) :
    (∫ x in Ioi r,
      Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by sorry
