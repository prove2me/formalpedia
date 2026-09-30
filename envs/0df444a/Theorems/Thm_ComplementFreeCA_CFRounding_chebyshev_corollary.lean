-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_chebyshev_corollary
-- name    : ComplementFreeCA.CFRounding.chebyshev_corollary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:04.443278+00:00
-- url     : https://prove2.me/theorems/876e854f-8af2-4c9a-bf11-0ded7e0f6d6b
-- title:
--   Lemma 3.2 — Chebyshev for sums of independent [0,1] variables: Pr[|X − μ| ≥ α] ≤ μ/α²
-- statement:
--   Let $X_1,\dots,X_N$ be independent random variables on a probability space, each taking values in $[0,1]$, let $X=X_1+\dots+X_N$ and $\mu=E[X]$. Then for every $\alpha>0$,
--   $$\Pr\big[|X-\mu|\ge\alpha\big]\le\frac{\mu}{\alpha^2}.$$
--
--   The paper uses this corollary of Chebyshev's inequality to show that the welfare of the rounded preallocation is unlikely to fall below a third of its expectation $OPT^*$.
--
--   **Formalization Note** The variables are real-valued, measurable, independent in the sense of Mathlib's `iIndepFun`, and take values in $[0,1]$ at every sample point; the number $N$ of variables is arbitrary. Expectation is the Bochner integral, which is the true expectation here because $X$ is bounded and measurable.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, Lemma 3.2

import Mathlib

namespace ComplementFreeCA.CFRounding

open MeasureTheory ProbabilityTheory

theorem chebyshev_corollary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hrange : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) (hα : 0 < α) :
    μ.real {ω | α ≤ |∑ i, X i ω - ∫ ω', ∑ i, X i ω' ∂μ|} ≤ (∫ ω', ∑ i, X i ω' ∂μ) / α ^ 2 := by sorry

end ComplementFreeCA.CFRounding
