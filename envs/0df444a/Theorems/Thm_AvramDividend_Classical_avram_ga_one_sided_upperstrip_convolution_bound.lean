-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_upperstrip_convolution_bound
-- name    : AvramDividend.Classical.avram_ga_one_sided_upperstrip_convolution_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:26:07.203852+00:00
-- url     : https://prove2.me/theorems/570895dc-681e-4a80-ac21-0f7b36bf2270
-- title:
--   One-sided convolution retains the exact finite-cap upper-strip indicator
-- statement:
--   Suppose a spatial generator source g is bounded above by c≥0 exactly when the evaluation point exceeds an inner cap b and by zero below b. A nonnegative unit-mass smoothing kernel supported on strictly positive shifts z>0, convolved by translations y−εz for ε>0, satisfies the same upper bound with the sharp indicator of the ORIGINAL point y>b. No artificial widening to b−ε is needed. This is the generator inequality in research v5 equation (25.4), after separately handling the favourable negative curvature atom.
-- source:
--   Sharp directional support: if y≤b and z>0, then y−εz<b; on y>b the generator's positive part is at most c. Multiply by a nonnegative unit kernel and integrate, preserving the literal cutoff level b.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_ga_one_sided_upperstrip_convolution_bound
    (μ : Measure ℝ) (φ g : ℝ → ℝ)
    (hφI : Integrable φ μ)
    (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε)
    (b y c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ u, g u ≤ if b < u then c else 0)
    (hInt : Integrable (fun z => φ z * g (y - ε*z)) μ) :
    (∫ z, φ z * g (y - ε*z) ∂μ) ≤
      if b < y then c else 0 := by sorry
