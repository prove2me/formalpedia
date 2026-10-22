-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_sdr_partition_bounds
-- name    : FlowsNetworks.Representatives.sdr_partition_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:34.468808+00:00
-- url     : https://prove2.me/theorems/3eddc210-07f7-47a8-a7af-a385f2f7af38
-- title:
--   Chapter II, Theorem 10.10 — SDRs meeting each block of a partition between assigned bounds
-- statement:
--   Let $P_1, \dots, P_p$ be a partition of $E = \{e_1, \dots, e_m\}$ into nonempty, pairwise disjoint blocks, and let $a_k, a'_k$ ($k = 1, \dots, p$) be integers with $0 \le a_k \le a'_k$. Let $S_1, \dots, S_n$ be subsets of $E$. For $U \subseteq \{1, \dots, p\}$ write $\bar U$ for its complement in $\{1, \dots, p\}$.
--
--   The sets $S_1, \dots, S_n$ have a system of distinct representatives $R$ with
--   $$a_k \le |R \cap P_k| \le a'_k \qquad (k = 1, \dots, p)$$
--   if and only if, for all $U \subseteq \{1, \dots, p\}$ and $V \subseteq \{1, \dots, n\}$,
--   $$\Bigl|\Bigl(\bigcup_{k \in U} P_k\Bigr) \cap \Bigl(\bigcup_{j \in V} S_j\Bigr)\Bigr| \ge \max\Bigl(|V| - \sum_{k \in \bar U} a'_k,\ |V| - n + \sum_{k \in U} a_k\Bigr). \tag{10.10}$$
--
--   The theorem is due to Hoffman and Kuhn. The first term of the maximum alone characterizes SDRs with $|R \cap P_k| \le a'_k$, the second alone SDRs with $|R \cap P_k| \ge a_k$.
--
--   **Formalization Note** $R$ is the set $\{r_1, \dots, r_n\}$ of an SDR $r$. The page prints the first union as $\bigcup_{j \in U} P_k$; the index is $k \in U$. The bounds are natural numbers, the blocks are nonempty `Finset`s that are pairwise disjoint and cover `Fin m`, and the inequality is evaluated in $\mathbb Z$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 68, Theorem 10.10

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 10.10 (p. 68), due to Hoffman and
Kuhn. Let `P₁, …, P_p` be a partition of `E = {e₁, …, e_m}` (nonempty, pairwise disjoint blocks
covering `E`) and let `a k ≤ a' k` (`k = 1, …, p`) be nonnegative integers. The subsets
`S₁, …, S_n` of `E` have a system of distinct representatives `R` with
`a k ≤ |R ∩ P_k| ≤ a' k` for every `k` if and only if
`(10.10)  |(⋃_{k ∈ U} P_k) ∩ (⋃_{j ∈ V} S_j)| ≥ max (|V| − ∑_{k ∈ Ū} a' k, |V| − n + ∑_{k ∈ U} a k)`
for all `U ⊆ {1, …, p}` and `V ⊆ {1, …, n}`, where `Ū` is the complement of `U` in `{1, …, p}`.
(The page prints the first union with index `j ∈ U`.) The set `R` is the image of the
representative list `r`. The arithmetic is in `ℤ`. -/
theorem sdr_partition_bounds {m n p : ℕ} (P : Fin p → Finset (Fin m))
    (hP_ne : ∀ k, (P k).Nonempty)
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hP_cover : ∀ e : Fin m, ∃ k, e ∈ P k)
    (a a' : Fin p → ℕ) (ha : ∀ k, a k ≤ a' k) (S : Fin n → Finset (Fin m)) :
    (∃ r : Fin n → Fin m, IsSDR S r ∧
        ∀ k, a k ≤ (Finset.univ.image r ∩ P k).card ∧ (Finset.univ.image r ∩ P k).card ≤ a' k) ↔
      ∀ (U : Finset (Fin p)) (V : Finset (Fin n)),
        ((U.biUnion P ∩ indexSet S V).card : ℤ) ≥
          max ((V.card : ℤ) - ∑ k ∈ Uᶜ, (a' k : ℤ))
            ((V.card : ℤ) - (n : ℤ) + ∑ k ∈ U, (a k : ℤ)) := by sorry

end FlowsNetworks.Representatives
