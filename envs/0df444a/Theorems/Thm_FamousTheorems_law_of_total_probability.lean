-- Prove2me | Theorems.Thm_FamousTheorems_law_of_total_probability
-- name    : FamousTheorems.law_of_total_probability
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:49.164132+00:00
-- url     : https://prove2.me/theorems/db6aad34-66b9-45c3-b2a4-182a231cabab
-- title:
--   The law of total probability
-- statement:
--   **The law of total probability.** Let $X$ be a measurable random variable with values in a finite set $\alpha$, and let $\mu$ be a finite measure. Then
--   $$\mu=\sum_{x\in\alpha}\mu(X=x)\;\mu(\,\cdot\mid X=x).$$
--   Evaluated on an event $A$, this is $\mu(A)=\sum_x\mu(X=x)\,\mu(A\mid X=x)$.
--
--   This formula conditions on the value of $X$ and splits into cases. It is used throughout probability, Bayesian inference and Markov chain analysis, and it underlies Bayes' theorem.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.sum_meas_smul_cond_fiber`. `ProbabilityTheory.cond μ s` is the conditional measure $\mu(\cdot\mid s)$. The identity is an equality of measures, with scalar multiplication by $\mu(X=x)\in[0,\infty]$. When $\mu(X=x)=0$ the conditional measure is $0$, so that term vanishes. $\alpha$ carries the discrete $\sigma$-algebra.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.sum_meas_smul_cond_fiber`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem law_of_total_probability {Ω α : Type*} {m : MeasurableSpace Ω} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x : α, μ (X ⁻¹' {x}) • ProbabilityTheory.cond μ (X ⁻¹' {x}) = μ := by sorry

end FamousTheorems
