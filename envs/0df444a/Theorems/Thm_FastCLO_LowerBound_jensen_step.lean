-- Prove2me | Theorems.Thm_FastCLO_LowerBound_jensen_step
-- name    : FastCLO.LowerBound.jensen_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:38.045648+00:00
-- url     : https://prove2.me/theorems/2daae76f-277e-4a42-bbe1-2d1354463381
-- title:
--   Proof of Theorem 3, p. 21 — E[(1 + c^N)^{−1}] ≥ ½ c^{−E N} for c ≥ 1 (the Jensen step)
-- statement:
--   Let $Q$ be a probability measure, let $c \ge 1$, and let $N \ge 0$ be a measurable, integrable random variable. Then
--   $$\mathbb E_Q\big[(1 + c^{N})^{-1}\big] \;\ge\; \tfrac12\,\mathbb E_Q\big[c^{-N}\big] \;\ge\; \tfrac12\, c^{-\mathbb E_Q N}.$$
--   The statement asserts the outer inequality $\tfrac12 c^{-\mathbb E_Q N} \le \mathbb E_Q[(1+c^N)^{-1}]$.
--
--   The first inequality holds because $c^N \ge 1$; the second is Jensen's inequality for the convex function $t \mapsto c^{-t}$. In the paper it is applied with $c = (1+\zeta)/(1-\zeta)$ and $N = |N^1_i - N^0_i|$, reducing the Bayes risk to the expected absolute difference of two counts.
--
--   **Formalization Note** The page writes both inequalities for the sum over $i$; the statement is the chained bound for one index and an arbitrary probability measure. Powers are real powers of the base $c \ge 1$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 3 (A.2), p. 21, the display after "Therefore,"

import Mathlib

open MeasureTheory

namespace FastCLO.LowerBound

/-- The Jensen step (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 3, p. 21, the display
after "Therefore,"), for one index `i`: for `c ≥ 1` and a nonnegative integrable random variable `N`,
`E[(1 + c^N)^{-1}] ≥ (1/2) E[c^{-N}] ≥ (1/2) c^{-E N}`.

Formalization Note: the page applies this with `c = (1+ζ)/(1−ζ)` and `N = |N¹_i − N⁰_i|`; here the
two inequalities are chained and stated for an arbitrary probability measure. Powers are `Real.rpow`
with base `c ≥ 1 > 0`. -/
theorem jensen_step {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 1 ≤ c) (N : Ω → ℝ) (hN : Measurable N) (hN0 : ∀ ω, 0 ≤ N ω)
    (hint : Integrable N Q) :
    (1 / 2) * c ^ (-(∫ ω, N ω ∂Q)) ≤ ∫ ω, (1 + c ^ N ω)⁻¹ ∂Q := by sorry

end FastCLO.LowerBound
