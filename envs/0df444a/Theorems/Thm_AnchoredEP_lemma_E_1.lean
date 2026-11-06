-- Prove2me | Theorems.Thm_AnchoredEP_lemma_E_1
-- name    : AnchoredEP.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:59.451803+00:00
-- url     : https://prove2.me/theorems/f61c6365-fd1c-44ab-b702-fde4bf8ec6c6
-- title:
--   Lemma E.1 — growth of sequences with $B_k^\alpha\ge c\sum_{j\le k}B_j$
-- statement:
--   Let $(B_k)_{k\ge1}$ be a positive, nondecreasing sequence of real numbers, and let $\alpha>1$ and $c>0$. If
--   $$
--   B_k^{\alpha}\ge c\sum_{j=1}^{k}B_j\qquad\text{for every }k\ge1,
--   $$
--   then for every $k\ge1$,
--   $$
--   B_k\ge\Big(\frac{\alpha-1}{\alpha}\,c\,k\Big)^{1/(\alpha-1)} .
--   $$
--   Applied with $\alpha=p/(p-1)$, it turns the stability estimate into polynomial growth of the cumulative step size.
--
--   Differences from the source:
--   - encoding: a sequence {B_k}_{k≥1} → B : ℕ → ℝ with every hypothesis and the conclusion for k ≥ 1; reason: the value B 0 is unused
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma E.1 ([BJLLS19, Lemma 12]), p.27

import Mathlib

namespace AnchoredEP

/-- **Lemma E.1 (sequence growth, [BJLLS19, Lemma 12]).** Jiang–Yoon, arXiv:2609.30212,
Lemma E.1, p.27: "Let `{B_k}_{k≥1}` be a positive, nondecreasing sequence. If there exist
constants `α > 1` and `c > 0` such that `B_k^α ≥ c ∑_{j=1}^k B_j` for every `k ≥ 1`, then
`B_k ≥ ((α − 1)/α · c k)^{1/(α−1)}`."

**Formalization Note.** The sequence is `B : ℕ → ℝ`, of which only the indices `k ≥ 1` matter; the
powers `B_k^α` and `(…)^{1/(α−1)}` are real powers (`Real.rpow`), with `α` real. -/
theorem lemma_E_1 (B : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → 0 < B k)
    (hmono : ∀ k, 1 ≤ k → B k ≤ B (k + 1)) (α c : ℝ) (hα : 1 < α) (hc : 0 < c)
    (hrec : ∀ k, 1 ≤ k → c * ∑ j ∈ Finset.Icc 1 k, B j ≤ B k ^ α) :
    ∀ k, 1 ≤ k → ((α - 1) / α * c * k) ^ (1 / (α - 1)) ≤ B k := by sorry

end AnchoredEP
