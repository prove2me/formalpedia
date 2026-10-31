-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_minOneTreeCost_eq_oneTreeLPValue
-- name    : CombOpt.HeldKarp.minOneTreeCost_eq_oneTreeLPValue
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:16.112858+00:00
-- url     : https://prove2.me/theorems/e7dcbdc1-d8a3-4cc9-8712-9bef779c3a64
-- title:
--   (7.7): the cost of a minimum 1-tree equals the 1-tree LP value (corrected: no loop at $v_1$, $S\ne\emptyset$ in (7.4))
-- statement:
--   Let $G=(V,E)$ be a finite graph, $v_1\in V$ a node with no loop at it, and $c\in\mathbb R^E$. Then the cost of a minimum 1-tree of $G$ (with respect to $v_1$) equals
--   $$\min\{c^Tx : x(\gamma(S))\le|S|-1\ (\emptyset\ne S\subseteq V,\ v_1\notin S),\ x(\gamma(V\setminus\{v_1\}))=|V|-2,\ 0\le x\le1,\ x(\delta(v_1))=2\},\qquad(7.7)$$
--   both sides being $+\infty$ when there is no 1-tree, respectively when (7.7) is infeasible.
--
--   This identifies the combinatorial 1-tree bound with the optimal value of a linear program, the link between the Held–Karp bound and the subtour relaxation.
--
--   Differences from the source:
--   - correction: any graph G → no loop at v_1; reason: counterexample: triangle v_1ab with costs 0 plus a loop at v_1 of cost −1; the loop is in no γ(S) with v_1 ∉ S and not in δ(v_1), so (7.7) sets it to 1 and has value −1, while every 1-tree costs 0
--   - generalization: G is the complete graph of the TSP model (§7.1, p. 241) → any finite graph with no loop at v_1, parallel edges allowed; reason: §7.3 takes "a graph G" in its boxes and in the Held-Karp method; a complete graph is simple, hence an instance, so the statement specializes to the complete case
--   - correction: (7.4) for all S ⊆ V with v_1 ∉ S → (7.4) for all nonempty S ⊆ V with v_1 ∉ S; reason: at S = ∅ the printed constraint reads 0 ≤ −1, so (7.7) as printed is always infeasible; counterexample: the triangle with costs 0 has 1-trees of cost 0
--   - encoding: cost of a minimum 1-tree; min of (7.7) → infima in EReal, +∞ on an empty set; reason: Lean convention; both minima are attained when their sets are nonempty
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.7), p. 260 (PDF p. 268)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_minOneTreeCost
import Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeLPValue

namespace CombOpt.HeldKarp

/-- **(7.7): the cost of a minimum 1-tree equals the optimal value of the 1-tree linear program
(corrected: no loop at v₁, S ≠ ∅ in (7.4)).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3,
p. 260 (PDF p. 268): "we can conclude that the cost of a minimum 1-tree in G is equal to
min {c^T x : x satisfies (7.4), (7.5), (7.6), and x(δ(v_1)) = 2}. (7.7)"

For a finite graph `G` with no loop at `v₁` and real costs `c`, the least cost of a 1-tree equals
the optimal value of (7.7), both in `EReal` (`⊤` when there is no 1-tree, resp. (7.7) is infeasible).

**Formalization Note.** Two corrections. (i) (7.4) is imposed for nonempty `S` (printed: all
`S ⊆ V` with `v₁ ∉ S`, which at `S = ∅` reads `0 ≤ −1`). (ii) No loop at `v₁`: such a loop is in no
`γ(S)` with `v₁ ∉ S` and not in `δ(v₁)`, so (7.7) lets it take value 1, and with negative cost the
LP drops below every 1-tree. Loops at other nodes are allowed (they are forced to 0 by (7.4) with
`S = {u}`). -/
theorem minOneTreeCost_eq_oneTreeLPValue {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : Graph V E) (v₁ : V) (hv₁ : ∀ e : E, G.ends e ≠ s(v₁, v₁))
    (c : E → ℝ) :
    G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁ := by sorry

end CombOpt.HeldKarp
