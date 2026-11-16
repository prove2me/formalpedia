-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_product_event_independent_centered_physical_gain
-- name    : AvramDividend.Classical.avram_b29_product_event_independent_centered_physical_gain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:00:34.312434+00:00
-- url     : https://prove2.me/theorems/ebfceff8-942f-4084-b672-5210ab982278
-- title:
--   On an independent Brownian and Poisson product probability space, a centred Brownian surrogate gives zero restricted physical gain on a Poisson no-jump event
-- statement:
--   On an exact independent product probability space μ.prod ν for Brownian and Poisson input sources, let the no-large-jump event depend measurably only on the Poisson coordinate, and let a physical mesh gain G_k agree on that event with an integrable mean-zero Brownian-only surrogate H_k. The product-coordinate independence follows from Mathlib ProbabilityTheory.indepFun_prod, so applying the already-Proved Avram B27 event-surrogate mean-zero result gives the original physical gain zero expectation on the no-large-jump event for every mesh k. This discharges the product independence mechanism required in the B25 two-channel source counterexample without assuming the original Levy model is already constructed or declaring physical increments independent under stopping.
-- source:
--   Mathlib ProbabilityTheory.indepFun_prod; Prove2Me accepted B27 independent surrogate event zero expectation theorem 933e918e; Brownian plus size-two Poisson physical two-channel obstruction (15 November 2026)

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b27_event_independent_surrogate_gain_mean_zero
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_b29_product_event_independent_centered_physical_gain
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set ΩN) (hA : MeasurableSet A)
    (H : ℕ → ΩB → ℝ) (hHm : ∀ k, Measurable (H k))
    (G : ℕ → ΩB × ΩN → ℝ)
    (hHI : ∀ k, Integrable (fun p : ΩB × ΩN => H k p.1) (μ.prod ν))
    (hSame : ∀ k, ∀ᵐ p ∂((μ.prod ν).restrict {p : ΩB × ΩN | p.2 ∈ A}),
      G k p = H k p.1)
    (hZero : ∀ k, (∫ p, H k p.1 ∂(μ.prod ν)) = 0) :
    ∀ k, (∫ p in {p : ΩB × ΩN | p.2 ∈ A},
      G k p ∂(μ.prod ν)) = 0 := by sorry
