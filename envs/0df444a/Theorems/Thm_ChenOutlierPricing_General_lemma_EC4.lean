-- Prove2me | Theorems.Thm_ChenOutlierPricing_General_lemma_EC4
-- name    : ChenOutlierPricing.General.lemma_EC4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:40:57.942084+00:00
-- url     : https://prove2.me/theorems/71a9d429-db89-4e81-b11b-2e7c79105273
-- title:
--   Lemma EC.4 — uniform Bernstein inequality for bounded martingale differences
-- statement:
--   Let $(w_j,\mathcal F_j)_{j\ge1}$ be an adapted martingale-difference sequence on a probability space, with $\mathbb E[w_j\mid\mathcal F_{j-1}]=0$ and $|w_j|\le c$ almost surely for a fixed $c>0$. Put $V_n^2=\sum_{j=1}^n\mathbb E[w_j^2\mid\mathcal F_{j-1}]$. For every $\epsilon,y>0$,
--   $$\Pr\{\exists n\ge1:\ \sum_{j=1}^n w_j\ge\epsilon,\ V_n^2\le y\}\le\exp\!\left(-\frac{\epsilon^2}{2(y+c\epsilon)}\right).$$
--   The event ranges over all positive times, not a fixed terminal time. Boundedness and adaptedness imply the integrability needed for conditional expectation.
--
--   Differences from the source:
--   - encoding: conditional probability Pr(|w_j|≤c | F_{j-1})=1 → the equivalent almost-sure bound |w_j|≤c; reason: conditional probability one and almost-sure membership agree; adaptation and the finite bound supply integrability
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, e-companion, p. ec10, Lemma EC.4

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ChenOutlierPricing.General

/-- Chen and Wang, e-companion, ec10, Lemma EC.4. -/
theorem lemma_EC4 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (w : ℕ → Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (hadapt : ∀ j, 1 ≤ j → Measurable[ℱ j] (w j))
    (hmean : ∀ j, 1 ≤ j → μ[w j | ℱ (j-1)] =ᵐ[μ] 0)
    (hbounded : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, |w j ω| ≤ c)
    (ε y : ℝ) (hε : 0 < ε) (hy : 0 < y) :
    μ.real {ω | ∃ n : ℕ, 1 ≤ n ∧
      ε ≤ ∑ j ∈ Finset.Icc 1 n, w j ω ∧
      (∑ j ∈ Finset.Icc 1 n, μ[fun ω' => (w j ω')^2 | ℱ (j-1)] ω) ≤ y} ≤
      Real.exp (-ε^2 / (2*(y+c*ε))) := by sorry

end ChenOutlierPricing.General
