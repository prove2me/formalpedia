-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_common_sdr
-- name    : FlowsNetworks.Representatives.common_sdr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:28.305214+00:00
-- url     : https://prove2.me/theorems/d14f67c9-c5a2-4409-be91-e46f5a3c70fa
-- title:
--   Chapter II, Corollary 10.9 — existence of a common system of distinct representatives
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ and $\mathcal T = \{T_1, \dots, T_n\}$ be two families of $n$ subsets of $E = \{e_1, \dots, e_m\}$. For $X, Y \subseteq \{1, \dots, n\}$ let $I(X)$ be the index set of $\bigcup_{j \in X} S_j$ and $I(Y)$ that of $\bigcup_{j \in Y} T_j$. A **common SDR** is a list of distinct elements $r_1, \dots, r_n$ together with a permutation $\sigma$ of $\{1, \dots, n\}$ such that $r_j \in S_j$ and $r_j \in T_{\sigma(j)}$ for every $j$.
--
--   A common SDR for $\mathcal S$ and $\mathcal T$ exists if and only if, for every $X, Y \subseteq \{1, \dots, n\}$,
--   $$|X| + |Y| \le n + |I(X) \cap I(Y)|. \tag{10.9}$$
--
--   This is the case $a_i = 0$, $a'_i = 1$ of Theorem 10.8; it extends Hall's theorem on common representatives of two partitions to arbitrary families.
--
--   **Formalization Note** The common SDR is a pair `(r, σ)` with `r` injective. All quantities are natural numbers; no subtraction occurs.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 68, Corollary 10.9

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.9 (p. 68). A common SDR exists for
`𝒮 = {S₁, …, S_n}` and `𝒯 = {T₁, …, T_n}` if and only if, for every `X, Y ⊆ {1, …, n}`,
`(10.9)  |X| + |Y| ≤ n + |I(X) ∩ I(Y)|`,
where `I(X)` is the index set of `⋃_{j ∈ X} S_j` and `I(Y)` that of `⋃_{j ∈ Y} T_j`. -/
theorem common_sdr {m n : ℕ} (S T : Fin n → Finset (Fin m)) :
    (∃ (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)), IsCommonSDR S T r σ) ↔
      ∀ X Y : Finset (Fin n),
        X.card + Y.card ≤ n + (indexSet S X ∩ indexSet T Y).card := by sorry

end FlowsNetworks.Representatives
