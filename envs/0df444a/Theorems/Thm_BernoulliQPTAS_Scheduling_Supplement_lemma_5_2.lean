-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_Supplement_lemma_5_2
-- name    : BernoulliQPTAS.Scheduling.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:08.603204+00:00
-- url     : https://prove2.me/theorems/25e98202-4607-4264-a967-37b953cc5ab0
-- title:
--   Lemma 5.2 — the greedy rule minimizes the surrogate objective over all adaptive orders
-- statement:
--   Let $m\ge2$ and $r=m-1$. Let $A$ be a multiset of $r$ nonnegative numbers (the $r$ largest realized processing times so far, padded with zeros) and $R$ a set of remaining jobs, $s=|R|$. For an adaptive order of $R$ (the next job may depend on all outcomes observed so far), let $D'_1,\dots,D'_s$ be the successive increments of $W_r$: when a job with realized processing time $x$ is started while the current multiset has minimum $\theta$, the increment is $\min\{x,\theta\}$, and $x$ is then inserted into the multiset, which keeps its $r$ largest values.
--
--   Fix distinct ranks $\rho(j)$. The greedy rule, which always picks a remaining job minimizing $(q_j\min\{p_j,\theta\},q_j,\rho(j))$ lexicographically, is a valid adaptive order of $R$, and for every valid adaptive order $o$ of $R$,
--
--   $$
--   \mathbb E_{\mathrm{greedy}}\Bigl[\sum_{i=1}^{s}(s-i)D'_i\Bigr]\le \mathbb E_{o}\Bigl[\sum_{i=1}^{s}(s-i)D'_i\Bigr].
--   $$
--
--   The lemma gives $H(G)\le H(\Pi)$ for every policy $\Pi$, which is the step both bounds of Theorem 5.1 rest on.
--
--   **Formalization Note** Adaptive orders are deterministic decision trees. By linearity of expectation, a randomized order is a mixture of deterministic ones, so the minimum is the same. $A$ is a list of $m-1$ nonnegative rationals.
--
--   Differences from the source:
--   - encoding: "over all adaptive orders" → over all deterministic adaptive decision trees valid for R; reason: a randomized order is a mixture of deterministic ones, so by linearity it cannot do better
--   - encoding: "for every multiset A" → every list of m − 1 nonnegative rationals; reason: processing times are rational; lists represent multisets, and the objective depends only on the multiset
--   - encoding: standing assumption m ≥ 2 of Section 5 (r = m − 1) → hypothesis 2 ≤ m; reason: same instances
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Lemma 5.2, p. 15 (Section 5.1 setting, p. 15)

import Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Greedy

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling

theorem lemma_5_2 {N m : ℕ} (I : Instance N m) (hm : 2 ≤ m)
    (ρ : Fin N → ℕ) (hρ : Function.Injective ρ)
    (A : List ℚ) (hA : A.length = m - 1) (hA0 : ∀ x ∈ A, 0 ≤ x)
    (R : Finset (Fin N)) (o : OrderTree N) (ho : ValidOrder R o) :
    ValidOrder R (greedyOrder I ρ R.card A R) ∧
      orderObjective I A R (greedyOrder I ρ R.card A R) ≤ orderObjective I A R o := by sorry

end BernoulliQPTAS.Scheduling.Supplement
