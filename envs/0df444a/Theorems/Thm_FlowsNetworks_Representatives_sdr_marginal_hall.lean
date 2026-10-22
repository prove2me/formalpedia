-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_sdr_marginal_hall
-- name    : FlowsNetworks.Representatives.sdr_marginal_hall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:29.778188+00:00
-- url     : https://prove2.me/theorems/7bdca05b-d0ea-452e-9aa0-6ac1834ae649
-- title:
--   Chapter II, Theorem 10.6 — the Hoffman–Kuhn theorem on SDRs containing prescribed marginal elements
-- statement:
--   Let $\mathcal S = \{S_1, \dots, S_n\}$ be a family of subsets of $E = \{e_1, \dots, e_m\}$ and let $M \subseteq E$ be a prescribed set of **marginal elements**. An SDR for $\mathcal S$ whose set of representatives contains $M$ exists if and only if both of the following hold:
--
--   1. **Hall's condition**: for every $X \subseteq \{1, \dots, n\}$, $\bigl|\bigcup_{j \in X} S_j\bigr| \ge |X|$;
--   2. for every $M' \subseteq M$,
--   $$\bigl|\{\, j : S_j \cap M' \neq \emptyset \,\}\bigr| \ge |M'|.$$
--
--   The theorem, due to Hoffman and Kuhn, replaces the sufficient condition of Mann and Ryser by a necessary and sufficient one; the second condition is Hall's condition for the elements of $M$ against the sets.
--
--   **Formalization Note** "The SDR contains $M$" is $M \subseteq \{r_1, \dots, r_n\}$, the image of the representative function. Hall's condition is stated for all finite index sets $X$, which is the book's "every union of $k$ sets contains at least $k$ elements, $k = 1, \dots, n$" ($X = \emptyset$ is trivial).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 62, Theorem 10.6

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 10.6 (p. 62), due to Hoffman and
Kuhn. An SDR for `𝒮 = {S₁, …, S_n}` that contains a prescribed set `M` of marginal elements exists
if and only if both Hall's condition (every union of `k` sets of `𝒮` contains at least `k`
distinct elements) and the following condition hold: for any `M' ⊆ M`, the number of sets `S_j`
that meet `M'` is at least `|M'|`. -/
theorem sdr_marginal_hall {m n : ℕ} (S : Fin n → Finset (Fin m)) (M : Finset (Fin m)) :
    (∃ r : Fin n → Fin m, IsSDR S r ∧ M ⊆ Finset.univ.image r) ↔
      ((∀ X : Finset (Fin n), X.card ≤ (indexSet S X).card) ∧
        ∀ M' ⊆ M, M'.card ≤ (Finset.univ.filter (fun j => (S j ∩ M').Nonempty)).card) := by sorry

end FlowsNetworks.Representatives
