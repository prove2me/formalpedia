-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_J_4
-- name    : CalendarDependentRM.lemma_J_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:34:30.784586+00:00
-- url     : https://prove2.me/theorems/ddb86308-6aaf-42b9-96e6-2280e8b3d24a
-- title:
--   Lemma J.4: a Bernoulli moment generating function bound
-- statement:
--   Let $Z$ be a Bernoulli random variable with mean $\mu$. Then for all $\lambda\in[0,1]$,
--
--   $$
--   E\{e^{\lambda(Z-\mu)}\}\le e^{\mu\lambda^2}.
--   $$
--
--   Unlike the Hoeffding bound, the exponent scales with the mean, which is what lets the concentration term in Lemma 5.3 scale with $c_i$.
--
--   Differences from the source: none.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma J.4, ER p.23 (PDF 45)

import Mathlib

open MeasureTheory

namespace CalendarDependentRM

/-- **Lemma J.4.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma J.4, Extended Results p. 23 (PDF p. 45):
if `Z` is Bernoulli with mean `µ`, then `E{e^{λ(Z − µ)}} ≤ e^{µλ²}` for all `λ ∈ [0, 1]`.

**Formalization Note** `Z` is a real random variable with values in `{0, 1}` almost surely and expectation `µ`. -/
theorem lemma_J_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : ∀ᵐ ω ∂P, Z ω = 0 ∨ Z ω = 1) {μ : ℝ}
    (hμ : ∫ ω, Z ω ∂P = μ) {lamb : ℝ} (hl : lamb ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, Real.exp (lamb * (Z ω - μ)) ∂P ≤ Real.exp (μ * lamb ^ 2) := by sorry

end CalendarDependentRM
