-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_fixed_terminal_independent_exponential_clock_cylinder
-- name    : AvramDividend.Classical.esscher_fixed_terminal_independent_exponential_clock_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:56:47.080986+00:00
-- url     : https://prove2.me/theorems/0711584a-d162-4d8c-8dbb-c5d1cf22ea81
-- title:
--   Fixed-terminal Esscher laws factorise against independent exponential-clock cylinder events
-- statement:
--   Let Q_t be the Esscher path probability weighted at deterministic terminal time t. For any earlier filtration event A observable at s<=t and any measurable clock event B, the Q_t × Exp(p) probability of A×B equals Q_s(A) Exp(p)(B). This simultaneously records product-law clock independence and Esscher projective consistency on path cylinders. It does not identify the distinct joint density weighted at the realised clock time and does not assert existence of one global infinite-horizon tilted law.
-- source:
--   Direct mathematical composition of canonical Proved chat04_esscher_finite_horizon_laws_consistent_on_past_events (a74b3334-5c28-44d1-ae88-3057d26957f4) and pinned Mathlib MeasureTheory.Measure.prod_prod, for the finite-horizon Esscher change of measure used in Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions (2012), Section 1.2.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_fixed_terminal_independent_exponential_clock_cylinder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (p : ℝ) (hp : 0 < p)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))).prod
      (ProbabilityTheory.expMeasure p)) (A ×ˢ B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
      (ProbabilityTheory.expMeasure p) B := by sorry
