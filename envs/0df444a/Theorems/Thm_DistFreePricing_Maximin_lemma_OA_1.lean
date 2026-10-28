-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_lemma_OA_1
-- name    : DistFreePricing.Maximin.lemma_OA_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:30.523882+00:00
-- url     : https://prove2.me/theorems/aa5a486a-aff0-4f9e-9ce4-5891aeb3fdaa
-- title:
--   Lemma OA.1, OA p. 9 — Cantelli's inequality: P(X ≤ µ − a) ≤ σ²/(σ² + a²) for a ≥ 0
-- statement:
--   **Cantelli's inequality (one-sided Chebyshev, left tail).** Let $X$ be a square-integrable random variable on a probability space with mean $\mu=\mathbb E[X]$ and variance $\sigma^2$, $\sigma\ge0$. Then for every $a\ge 0$ (with $\sigma^2+a^2>0$, so that the bound is defined)
--
--   $$\mathbb P(X<\mu-a)\le\mathbb P(X\le\mu-a)\le\frac{\sigma^2}{\sigma^2+a^2}.$$
--
--   If $\sigma>0$ then, equivalently, with $a=k\sigma$, for every $k\ge 0$
--
--   $$\mathbb P(X<\mu-k\sigma)\le\mathbb P(X\le\mu-k\sigma)\le\frac{1}{1+k^2},$$
--
--   and the same $k$-form holds for a valuation $V$ with law $F\in\mathscr F$ (nonnegative support, mean $\mu$, second moment $\mu^2+\sigma^2$): $F((-\infty,\mu-k\sigma))\le F((-\infty,\mu-k\sigma])\le 1/(1+k^2)$.
--
--   This is the only probabilistic input of the paper's distribution-free bounds: it controls the mass below a price $\mu-k\sigma$, hence the fraction of customers lost at that price.
--
--   **Formalization Note** Probabilities are `measureReal`; the variance is `ProbabilityTheory.variance`. The $k$-form uses the paper's standing $\sigma>0$ (pp. 8–9).
--
--   Differences from the source:
--
--   - encoding: a random variable X that has mean μ and standard deviation σ → X ∈ L²(P) on a probability space, ∫ X dP = μ, variance X P = σ², σ ≥ 0; reason: having a standard deviation means a finite second moment; same instances
--   - encoding: for all a ≥ 0 → for all a ≥ 0 with 0 < σ² + a²; reason: at σ = a = 0 the bound σ²/(σ² + a²) is 0/0; this excludes only that undefined case
--   - reading: "Equivalently, … ≤ 1/(1+k²) for any k ≥ 0" → the k-form under 0 < σ; reason: the paper's standing σ > 0 (pp. 8–9); the substitution a = kσ needs it, and at σ = 0 the k-form is false (X = μ a.s., P(X ≤ μ) = 1 > 1/(1+k²) for k > 0)
--   - reading: the k-form is written for the valuation V → stated both for X and for every law F ∈ 𝓕 (Iio/Iic masses of F); reason: the paper uses the k-form for the valuation law in Theorem 1; both readings are given
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), Lemma OA.1, OA p. 9

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Lemma OA.1 (Cantelli's inequality, OA p. 9), for a square-integrable random variable with
mean `μ` and standard deviation `σ ≥ 0`: the `a`-form for every `a ≥ 0` at which the bound
`σ²/(σ² + a²)` is defined, and, under the paper's standing `σ > 0`, the equivalent `k`-form, also
for a valuation law `F ∈ 𝓕`. -/
theorem lemma_OA_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (μ σ : ℝ) (hμ : ∫ ω, X ω ∂P = μ) (hσ : 0 ≤ σ)
    (hvar : ProbabilityTheory.variance X P = σ ^ 2) :
    (∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) ∧
    (0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) ∧
    (0 < σ → ∀ F ∈ valClass μ σ, ∀ k : ℝ, 0 ≤ k →
      F.real (Set.Iio (μ - k * σ)) ≤ F.real (Set.Iic (μ - k * σ)) ∧
        F.real (Set.Iic (μ - k * σ)) ≤ 1 / (1 + k ^ 2)) := by sorry

end DistFreePricing.Maximin
