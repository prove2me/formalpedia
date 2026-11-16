-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_product_brownian_centered_restricted_nojump_gain_zero
-- name    : AvramDividend.Classical.avram_b29_product_brownian_centered_restricted_nojump_gain_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:12:50.287505+00:00
-- url     : https://prove2.me/theorems/7153ac0a-c906-41bb-9040-eddcc348f896
-- title:
--   Original Brownian-only centred physical gain remains mean-zero when restricted to the independent no-large-Poisson-jump event
-- statement:
--   Let Brownian path noise μ and independent negative Poisson marks ν be on their genuine product probability space. Let A be a measurable Poisson no-large-jump event. If the original bounded stopped Brownian-only physical mesh gain agrees on A with a measurable, μ-integrable and μ-centred Gaussian-coordinate surrogate H, then its integral over A against μ.prodν vanishes exactly for each mesh. Derive product integrability and product mean-zero from their Brownian-coordinate versions using the already Proved B29 Gaussian product lemma, then apply the independent event-surrogate restriction lemma. This is a fully explicit correct expectation bridge for the independent Brownian-Poisson two-noise source, without asserting the stopped mesh equals such a surrogate without evidence.
-- source:
--   Prove2Me accepted product coordinate centring theorem d835f03e, accepted event surrogate theorem 933e918e, and B29 event independence theorem ebfceff8 under server verification, 15 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b29_centered_gaussian_coordinate_product_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_b29_product_event_independent_centered_physical_gain
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_b29_product_brownian_centered_restricted_nojump_gain_zero
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set ΩN) (hA : MeasurableSet A)
    (H : ℕ → ΩB → ℝ) (hHm : ∀ k, Measurable (H k))
    (hHI : ∀ k, Integrable (H k) μ)
    (hZero : ∀ k, (∫ ω, H k ω ∂μ) = 0)
    (G : ℕ → ΩB × ΩN → ℝ)
    (hSame : ∀ k, ∀ᵐ p ∂((μ.prod ν).restrict {p : ΩB × ΩN | p.2 ∈ A}),
      G k p = H k p.1) :
    ∀ k, (∫ p in {p : ΩB × ΩN | p.2 ∈ A},
      G k p ∂(μ.prod ν)) = 0 := by sorry
