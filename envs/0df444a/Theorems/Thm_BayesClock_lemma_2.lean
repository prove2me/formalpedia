-- Prove2me | Theorems.Thm_BayesClock_lemma_2
-- name    : BayesClock.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:23.239734+00:00
-- url     : https://prove2.me/theorems/4ad87044-d1fb-4bf9-920a-fa32a20ef940
-- title:
--   Lemma 2: for $k\ge2$ the count stays within a factor $10$ of its mean below the threshold, with probability $\ge1-2/k^8$
-- statement:
--   Let $S$ be a set of bidders, $k\ge2$ an integer, and $t\ge 0$ such that $\mathbb E_v[|S(x,v)|]\ge\log k$ for every $x\in[0,t)$; this holds in particular if $\mathbb E_v[|S(t,v)|]=\log k$. Then
--
--   $$\Pr_v\big[\exists x\in[0,t):|S(x,v)|>10\cdot\mathbb E_v[|S(x,v)|]\big]\le\frac{2}{k^8}.$$
--
--   The bound depends on $k$ only, so it is an $o(1/k^2)$ uniform over $S$, $t$ and the distributions. It allows a union bound over the $k$ maximal sets.
--
--   **Formalization Note** The probability is the outer measure of the event under the product law; no measurability is assumed.
--
--   Differences from the source:
--   - generalization: o(1/k²) for a t with E[|S(t, v)|] = log k → the explicit bound 2/k⁸ for every t with E[|S(x, v)|] ≥ log k on [0, t); reason: E[|S(t, v)|] = log k implies the hypothesis by monotonicity, it also covers footnote 2, and 2/k⁸ is o(1/k²) uniformly
--   - generalization: log k = log₂ k with k the number of maximal sets → ln k (Real.log) with k any integer ≥ 2; reason: the lemma uses k only through log k; ln k ≤ log₂ k, so the Lean hypothesis is implied by the paper's, and the paper's k is one instance
--   - encoding: o(·) as k → ∞ → 2 ≤ k; reason: the asymptotic statement is about large k, and at k = 1, log k = 0
--   - encoding: values are real, S any bidder set → values in ℝ≥0, law a product of probability measures on ℝ≥0; reason: values are nonnegative in the paper
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Lemma 2, p.7

import Mathlib
import Definitions.Def_BayesClock_aboveSet
import Definitions.Def_BayesClock_expectedAbove

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Lemma 2, Feldman et al., *Bayesian and Randomized Clock Auctions*, arXiv:2202.09291v1, p.7:
`Pr_v[∃ x ∈ [0, t) : |S(x, v)| > 10 · E_v[|S(x, v)|]] = o(1/k²)`.

**Formalization Note** The paper's `o(1/k²)` is stated with the explicit rate `2 / k⁸`, which depends
on `k` only, so it is uniform in `S`, `t` and the laws. The hypothesis on `t` is implied by
`E_v[|S(t, v)|] = log k`, because `x ↦ E_v[|S(x, v)|]` is non-increasing, and it also holds at the
threshold of footnote 2. The event is not assumed measurable: `Measure.pi ν` is applied as an outer
measure. `log` in the hypothesis is the natural logarithm `Real.log`; the paper's `log` is base 2, and
`ln k ≤ log₂ k`, so the hypothesis is weaker than the paper's. `k` is any integer `≥ 2`. -/
theorem lemma_2 {N : Type*} [Fintype N] (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (S : Finset N) (k : ℕ) (hk : 2 ≤ k) (t : ℝ≥0)
    (ht : ∀ x, x < t → ENNReal.ofReal (Real.log k) ≤ expectedAbove ν S x) :
    Measure.pi ν {v | ∃ x, x < t ∧ 10 * expectedAbove ν S x < ((aboveSet S x v).card : ℝ≥0∞)} ≤
      ENNReal.ofReal (2 / (k : ℝ) ^ 8) := by sorry

end BayesClock
