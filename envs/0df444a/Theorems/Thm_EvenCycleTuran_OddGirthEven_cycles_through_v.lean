-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_cycles_through_v
-- name    : EvenCycleTuran.OddGirthEven.cycles_through_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:14.978177+00:00
-- url     : https://prove2.me/theorems/85ea4f93-9a08-4217-82fe-e34fb1504202
-- title:
--   §6.2 — odd cycles through a vertex equal edges in its outer layer
-- statement:
--   Let $l\ge2$, and suppose a finite simple graph $G$ has no cycles of length $3,\ldots,2l$. For each vertex $v$, no edge has both endpoints in $N_i(v)$ when $i<l$. Moreover,
--
--   $$\#\{C_{2l+1}\text{ copies containing }v\}=|E(G[N_l(v)])|.$$
--
--   This identity converts local odd-cycle counts into edge counts inside distance layers, as used in Claim 18 and the upper bound.
--
--   **Formalization Note** The layer uses extended distance, so unreachable vertices belong to no finite layer. Copies of cycles are unlabelled subgraphs.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 27, §6.2, paragraph preceding Claim 18

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- The layer identity preceding Claim 18, p. 27. -/
theorem cycles_through_v (l : ℕ) (hl : 2 ≤ l)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l)) G) (v : V) :
    (∀ i : ℕ, i < l → edgesInside G (layer G v i) = 0) ∧
    cyclesAt G l v = edgesInside G (layer G v l) := by sorry

end EvenCycleTuran.OddGirthEven
