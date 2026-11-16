-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a534_discounted_positive_endpoint_L1
-- name    : AvramDividend.Classical.avram_ga_a534_discounted_positive_endpoint_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:21:42.4227+00:00
-- url     : https://prove2.me/theorems/5d7b3041-2830-48ae-b95e-281749689d9c
-- title:
--   Discounted Gaussian endpoint with one-sided HJB exponential upper bound has integrable positive part
-- statement:
--   The positive part of a nonnegatively discounted value at a nonnegative random endpoint is integrable when the discount lies between zero and one, the value has a one-sided exponential upper bound, the exponential moment exists and the positive part is almost-everywhere strongly measurable.
-- source:
--   Pointwise envelope max(E*w(Z),0) ≤ K*exp(theta*Z), with E in [0,1], followed by Integrable.mono_nonneg. Used for the original clipped Gaussian postpayment source cells.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a534_discounted_positive_endpoint_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (Z E : Ω → ℝ) (θ K : ℝ)
    (hK : 0 ≤ K) (h0 : w 0 ≤ K)
    (hupper : ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hE : ∀ᵐ ω ∂P, 0 ≤ E ω ∧ E ω ≤ 1)
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (E ω * w (Z ω)) (0 : ℝ)) P) :
    Integrable (fun ω => max (E ω * w (Z ω)) (0 : ℝ)) P := by sorry
