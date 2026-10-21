-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_sdr_marginal_index
-- name    : FlowsNetworks.Representatives.sdr_marginal_index
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:36.944117+00:00
-- url     : https://prove2.me/theorems/5f35b262-2ee9-4a22-a540-f3ee4bfa0531
-- title:
--   Chapter II, Corollary 10.7 — SDRs containing prescribed marginal elements, via index sets
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ be a family of subsets of $E = \{e_1, \dots, e_m\}$ and let $M = \{e_{i_1}, \dots, e_{i_\ell}\}$ be a prescribed set of $\ell$ marginal elements with index set $L = \{i_1, \dots, i_\ell\}$. For $X \subseteq \{1, \dots, n\}$ let $I(X)$ be the index set of $\bigcup_{j \in X} S_j$.
--
--   An SDR for $\mathcal S$ that contains $M$ exists if and only if, for every $X \subseteq \{1, \dots, n\}$,
--   $$|X| \le \min\bigl(n - \ell + |L \cap I(X)|,\ |I(X)|\bigr). \tag{10.5}$$
--
--   This is the special case $a_i = 1$ for $i \in L$, $a_i = 0$ otherwise, $a'_i = 1$ for all $i$, of the SRR theorem (Theorem 10.5); it involves only subfamilies of $\mathcal S$.
--
--   **Formalization Note** Since $E$ is `Fin m`, the index set $L$ of $M$ is $M$ itself and $\ell = |M|$. The inequality is evaluated in $\mathbb Z$, so $n - \ell$ may be negative (then no such SDR exists and $X = \emptyset$ violates (10.5)).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 63, Corollary 10.7

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.7 (p. 63). An SDR for
`𝒮 = {S₁, …, S_n}` that contains a prescribed set `M = {e_{i₁}, …, e_{i_ℓ}}` of marginal elements
exists if and only if, for every `X ⊆ {1, …, n}`,
`(10.5)  |X| ≤ min (n − ℓ + |L ∩ I(X)|, |I(X)|)`,
where `L = {i₁, …, i_ℓ}` is the index set of `M` (here `M` itself, as `E = Fin m`), `ℓ = |M|`,
and `I(X)` is the index set of `⋃_{j ∈ X} S_j`. The arithmetic is in `ℤ`. -/
theorem sdr_marginal_index {m n : ℕ} (S : Fin n → Finset (Fin m)) (M : Finset (Fin m)) :
    (∃ r : Fin n → Fin m, IsSDR S r ∧ M ⊆ Finset.univ.image r) ↔
      ∀ X : Finset (Fin n),
        (X.card : ℤ) ≤ min ((n : ℤ) - (M.card : ℤ) + ((M ∩ indexSet S X).card : ℤ))
          ((indexSet S X).card : ℤ) := by sorry

end FlowsNetworks.Representatives
