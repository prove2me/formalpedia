-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_srr_existence
-- name    : FlowsNetworks.Representatives.srr_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:25.290881+00:00
-- url     : https://prove2.me/theorems/a9fb4767-1a81-4bfa-8fa6-ca4eaec5b4ce
-- title:
--   Chapter II, Theorem 10.5 — existence of a system of restricted representatives
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ be a family of subsets of $E = \{e_1, \dots, e_m\}$, and let $a_i, a'_i$ be integers with $0 \le a_i \le a'_i$ ($i = 1, \dots, m$). For $X \subseteq \{1, \dots, n\}$ let $I(X) \subseteq \{1, \dots, m\}$ be the index set of $\bigcup_{j \in X} S_j$.
--
--   A system of restricted representatives for $\mathcal S$ in which $e_i$ occurs at least $a_i$ and at most $a'_i$ times exists if and only if, for every subset $X$ of $\{1, \dots, n\}$,
--   $$|X| \le \min\Bigl(n - \sum_{i=1}^m a_i + \sum_{i \in I(X)} a_i,\ \sum_{i \in I(X)} a'_i\Bigr). \tag{10.1}$$
--
--   With $a_i = 0$ and $a'_i = 1$ for all $i$, (10.1) is Hall's condition and an SRR is an SDR. The first term alone characterizes lists in which each $e_i$ occurs at least $a_i$ times, the second alone lists in which each occurs at most $a'_i$ times.
--
--   **Formalization Note** The bounds are natural numbers (the page leaves integrality implicit; with real bounds the statement fails, see finding F1). The inequality is evaluated in $\mathbb Z$. The case $X = \emptyset$ gives $\sum_i a_i \le n$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 59, Theorem 10.5

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 10.5 (p. 59). An SRR for
`𝒮 = {S₁, …, S_n}` in which `eᵢ` occurs at least `a i` and at most `a' i` times
(`0 ≤ a i ≤ a' i`, integers) exists if and only if, for every subset `X` of the indices
`{1, …, n}`,
`(10.1)  |X| ≤ min (n − ∑_{i=1}^m a i + ∑_{i ∈ I(X)} a i, ∑_{i ∈ I(X)} a' i)`,
where `I(X)` is the index set of `⋃_{j ∈ X} S_j`. The arithmetic is in `ℤ`. -/
theorem srr_existence {m n : ℕ} (S : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ a' i) :
    (∃ r : Fin n → Fin m, IsSRR S a a' r) ↔
      ∀ X : Finset (Fin n),
        (X.card : ℤ) ≤ min ((n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ indexSet S X, (a i : ℤ))
          (∑ i ∈ indexSet S X, (a' i : ℤ)) := by sorry

end FlowsNetworks.Representatives
