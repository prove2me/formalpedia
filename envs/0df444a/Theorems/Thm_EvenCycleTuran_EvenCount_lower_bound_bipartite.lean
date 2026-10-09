-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_lower_bound_bipartite
-- name    : EvenCycleTuran.EvenCount.lower_bound_bipartite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:36.003614+00:00
-- url     : https://prove2.me/theorems/f61798ad-bd0a-411c-b5bb-d81138372a3f
-- title:
--   Theorem 10 proof, p. 9 — K_{k−1,n−k+1} is C_{2k}-free and has C(k−1,l)C(n−k+1,l)·l!·l!/(2l) copies of C_{2l}
-- statement:
--   Let $2\le l<k$ and $n\ge k-1$. The complete bipartite graph $K_{k-1,n-k+1}$ contains no cycle of length $2k$, and the number of its subgraphs isomorphic to $C_{2l}$ is
--   $$\mathcal N(C_{2l},K_{k-1,n-k+1})=\frac{1}{2l}\binom{k-1}{l}\binom{n-k+1}{l}\,l!\,l!.$$
--
--   This is the construction behind the second bound of Theorem 10: since $\binom{k-1}{l}l!=(k-1)_l$ and $\binom{n-k+1}{l}l!=(1+o(1))n^l$, it gives $\mathrm{ex}(n,C_{2l},C_{2k})\ge(1+o(1))\frac{(k-1)_l}{2l}n^l$.
--
--   **Formalization Note** The count is stated multiplied by $2l$ to avoid division in $\mathbb N$. The hypothesis $n\ge k-1$ makes $n-(k-1)$ the true size of the second class.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, proof of Theorem 10, first paragraph

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem lower_bound_bipartite (l k n : ℕ) (hl : 2 ≤ l) (hlk : l < k) (hn : k - 1 ≤ n) :
    EvenCycleTuran.C4Count.CycleFree {2 * k} (EvenCycleTuran.C4Count.bipGraph n (k - 1)) ∧
      2 * l * (EvenCycleTuran.C4Count.bipGraph n (k - 1)).copyCount (cycleGraph (2 * l)) =
        (k - 1).choose l * (n - (k - 1)).choose l * l.factorial * l.factorial := by sorry

end EvenCycleTuran.EvenCount
