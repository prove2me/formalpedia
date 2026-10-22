-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_sdr_of_degree_bound
-- name    : FlowsNetworks.Representatives.sdr_of_degree_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:29.216789+00:00
-- url     : https://prove2.me/theorems/3e56e140-3341-4f2b-9fd8-6578cab0e461
-- title:
--   Chapter II, Corollary 10.2 — an SDR exists when (n − 1)M < S
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ be a family of subsets of $E = \{e_1, \dots, e_m\}$. Suppose $S_j$ contains $s_j$ elements ($j = 1, \dots, n$), the element $e_i$ occurs in $r_i$ of the sets $S_j$ ($i = 1, \dots, m$), and put
--   $$S = \sum_{j=1}^n s_j = \sum_{i=1}^m r_i, \qquad M = \max(r_1, \dots, r_m, s_1, \dots, s_n).$$
--   If
--   $$(n - 1)\, M < S,$$
--   then $\mathcal S$ has a system of distinct representatives.
--
--   This is a sufficient condition for Hall's condition stated purely in terms of the set sizes and element frequencies; Corollary 10.3 (regular families) follows from it at once.
--
--   **Formalization Note** The page prints the maximum as $\max(r_1, \dots, r_n, s_1, \dots, s_n)$, but the $r$'s are indexed by $i = 1, \dots, m$; the maximum is taken over all $r_i$ and all $s_j$ (read literally with $n < m$ the statement is false; see finding F2). $M$ is a maximum of natural numbers (0 when both lists are empty), and the inequality is evaluated in $\mathbb Z$, so $n - 1$ does not truncate at $n = 0$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 58, Corollary 10.2

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.2 (p. 58). Let `S_j` contain
`s j` elements (`j = 1, …, n`), let `eᵢ` occur in `r i` of the sets `S_j` (`i = 1, …, m`), let
`𝕊 = ∑ⱼ s j` and `M = max(r₁, …, r_m, s₁, …, s_n)`. If `(n − 1) M < 𝕊`, then `𝒮` has an SDR.
(The page prints the maximum over `r₁, …, r_n`; the `r`'s are indexed by `i = 1, …, m`, and the
maximum is taken over all of them.) -/
theorem sdr_of_degree_bound {m n : ℕ} (S : Fin n → Finset (Fin m))
    (s : Fin n → ℕ) (hs : ∀ j, s j = (S j).card)
    (r : Fin m → ℕ) (hr : ∀ i, r i = (Finset.univ.filter (fun j => i ∈ S j)).card)
    (M : ℕ) (hM : M = max (Finset.univ.sup r) (Finset.univ.sup s))
    (hlt : ((n : ℤ) - 1) * (M : ℤ) < ∑ j, (s j : ℤ)) :
    ∃ f : Fin n → Fin m, IsSDR S f := by sorry

end FlowsNetworks.Representatives
