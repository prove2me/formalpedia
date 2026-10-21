-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_common_srr_theorem
-- name    : FlowsNetworks.Representatives.common_srr_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:48.005893+00:00
-- url     : https://prove2.me/theorems/10c572a1-0c49-446f-993f-9f7642d03b05
-- title:
--   Chapter II, Theorem 10.8 — existence of a common system of restricted representatives
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ and $\mathcal T = \{T_1, \dots, T_n\}$ be two families of $n$ subsets of $E = \{e_1, \dots, e_m\}$, and let $a_i, a'_i$ be integers with $0 \le a_i \le a'_i$ ($i = 1, \dots, m$). For $X, Y \subseteq \{1, \dots, n\}$ let $I(X)$ be the index set of $\bigcup_{j \in X} S_j$ and $I(Y)$ that of $\bigcup_{j \in Y} T_j$.
--
--   A **common SRR** is one list $r_1, \dots, r_n$ of elements of $E$ together with a permutation $\sigma$ of $\{1, \dots, n\}$ such that $r_j \in S_j$ and $r_j \in T_{\sigma(j)}$ for every $j$, in which each $e_i$ occurs at least $a_i$ and at most $a'_i$ times.
--
--   A common SRR exists if and only if, for every $X, Y \subseteq \{1, \dots, n\}$,
--   $$|X| + |Y| \le n - \sum_{i=1}^m a_i + \sum_{i \in I(X) \cup I(Y)} a_i + \sum_{i \in I(X) \cap I(Y)} a'_i. \tag{10.8}$$
--
--   With $a_i = 0$, $a'_i = 1$ it gives the condition for a common SDR (Corollary 10.9); with $\mathcal T$ consisting of $n$ copies of $E$ it contains the single-family SRR theorem.
--
--   **Formalization Note** The bounds are natural numbers (the page leaves integrality implicit; with real bounds the statement fails, see findings F1 and F3). The pair $(r, \sigma)$ encodes the book's network of Fig. 10.2: each representative represents exactly one $S_j$ and one $T_k$. The statement is self-contained: it writes out the clauses of the definition `IsCommonSRR` and takes $I(X)$ as `X.biUnion S`, the same as `indexSet S X`. The inequality is evaluated in $\mathbb Z$; $X = Y = \emptyset$ gives $\sum_i a_i \le n$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 67, Theorem 10.8

import Mathlib

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 10.8 (p. 67). A common SRR in which
`eᵢ` (`i = 1, …, m`) occurs at least `a i` times and at most `a' i` times (`0 ≤ a i ≤ a' i`,
integers) exists for `𝒮 = {S₁, …, S_n}` and `𝒯 = {T₁, …, T_n}` if and only if, for every
`X, Y ⊆ {1, …, n}`,
`(10.8)  |X| + |Y| ≤ n − ∑_{i=1}^m a i + ∑_{i ∈ I(X) ∪ I(Y)} a i + ∑_{i ∈ I(X) ∩ I(Y)} a' i`,
where `I(X)` is the index set of `⋃_{j ∈ X} S_j` and `I(Y)` that of `⋃_{j ∈ Y} T_j`. A common SRR
is one list `r₁, …, r_n` in which `r j` represents `S j` and `T (σ j)` for a permutation `σ`
(the predicate `IsCommonSRR` of the mission's definitions, written out here so that the statement
is self-contained; `I(X)` is `X.biUnion S`, i.e. `indexSet S X`). The arithmetic is in `ℤ`. -/
theorem common_srr_theorem {m n : ℕ} (S T : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ a' i) :
    (∃ (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
        (∀ j, r j ∈ S j ∧ r j ∈ T (σ j)) ∧
        ∀ i, a i ≤ (Finset.univ.filter (fun j => r j = i)).card ∧
          (Finset.univ.filter (fun j => r j = i)).card ≤ a' i) ↔
      ∀ X Y : Finset (Fin n),
        (X.card : ℤ) + (Y.card : ℤ) ≤
          (n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ X.biUnion S ∪ Y.biUnion T, (a i : ℤ)
            + ∑ i ∈ X.biUnion S ∩ Y.biUnion T, (a' i : ℤ) := by sorry

end FlowsNetworks.Representatives
