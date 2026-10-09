-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthOdd_cycles_through_v
-- name    : EvenCycleTuran.OddGirthOdd.cycles_through_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:26:28.7582+00:00
-- url     : https://prove2.me/theorems/d0beb49d-0099-45c5-9dfd-40dd6c5453fe
-- title:
--   Proof of Theorem 18, pp. 28–29 — every C_{2l+1} through v uses exactly one edge inside N_l(v)
-- statement:
--   Let $k > l \ge 2$ and let $G$ be a finite graph containing no cycle of length $3, 4, \dots, 2l$ or $2k+1$. Let $v$ be any vertex and $N_i(v)$ the set of vertices at distance exactly $i$ from $v$. Then:
--
--   1. for every $i < l$, no edge of $G$ has both endpoints in $N_i(v)$;
--   2. every copy of $C_{2l+1}$ in $G$ that contains $v$ has exactly one edge with both endpoints in $N_l(v)$;
--   3. consequently,
--   $$\#\{\text{copies of } C_{2l+1} \text{ containing } v\} \le \#\{\text{edges of } G \text{ inside } N_l(v)\}.$$
--
--   This reduces the upper bound of Theorem 18 to counting edges inside the $l$-th distance layer (Claim 19).
--
--   **Formalization Note** The graph-free hypothesis is the one on the page: $\mathcal C_{2l} \cup \{C_{2k+1}\}$-free. Copies are unlabelled subgraphs, and $N_i(v)$ uses graph distance.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, pp. 28–29, proof of Theorem 18, upper bound, first paragraph

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting

namespace EvenCycleTuran.OddGirthOdd

/-- Proof of Theorem 18, pp. 28–29: in a graph with no cycle of length 3, …, 2l or 2k+1, no edge lies
inside `N_i(v)` for `i < l`, every copy of `C_{2l+1}` through `v` has exactly one edge inside
`N_l(v)`, and so the number of such copies is at most the number of edges inside `N_l(v)`. -/
theorem cycles_through_v (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : CycleFree (Set.Icc 3 (2 * l) ∪ {2 * k + 1}) G) (v : V) :
    (∀ i : ℕ, i < l → edgesInside G (layer G v i) = 0) ∧
    (∀ S : G.Subgraph, Nonempty (SimpleGraph.cycleGraph (2 * l + 1) ≃g S.coe) →
      v ∈ S.verts →
      ∃! e : Sym2 V, e ∈ S.edgeSet ∧ ∀ x ∈ e, x ∈ layer G v l) ∧
    cyclesAt G l v ≤ edgesInside G (layer G v l) := by sorry

end EvenCycleTuran.OddGirthOdd
