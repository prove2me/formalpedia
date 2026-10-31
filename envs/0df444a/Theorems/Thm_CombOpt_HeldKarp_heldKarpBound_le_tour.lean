-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_heldKarpBound_le_tour
-- name    : CombOpt.HeldKarp.heldKarpBound_le_tour
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:41.988308+00:00
-- url     : https://prove2.me/theorems/19bfb2fd-c50e-4ce4-a137-f8fa8cafd509
-- title:
--   Held–Karp Bound (p. 255): $2\sum_v y_v + C$ is a lower bound for the TSP (corrected: no loop on one node)
-- statement:
--   Let $G=(V,E)$ be a finite graph with real edge costs $c$, let $v_1\in V$, and for each node $v$ let $y_v$ be a real number. For each edge $e$ with ends $u,v$ let $\bar c_e=c_e-y_u-y_v$, and let $C$ be the 1-tree bound of $G$ (with respect to $v_1$) for the costs $\bar c$. Assume $G$ has no loop or has at least two nodes. Then for every tour $T$ of $G$,
--   $$2\sum_{v\in V}y_v + C \le \sum_{e\in T}c_e ,$$
--   i.e. $2\sum_v y_v + C$ is a lower bound for the TSP on $G$ with respect to the original costs $c$.
--
--   Altering the costs by node numbers leaves the TSP unchanged but can raise the 1-tree bound; this is the Held–Karp lower bounding technique.
--
--   Differences from the source:
--   - correction: any graph G → G has no loop, or |V| ≥ 2; reason: counterexample: one node v_1 with a loop of cost 0; the loop is a tour of cost 0, but δ(v_1) = ∅ so C = +∞ and the bound is +∞ for every y
--   - encoding: minima A, B (and the bound) over possibly empty sets → infima in EReal, +∞ on an empty set; reason: Lean convention; on every instance where the book's minima exist they are the same values, and +∞ is the natural value of an empty minimum
--   - encoding: spanning tree of the graph G \ v_1 → edge set of G avoiding v_1, connecting all nodes ≠ v_1 by paths in it, with no circuit; reason: G \ v_1 has the nodes V \ {v_1} and the edges of G not incident with v_1, so these are the same edge sets
--   - encoding: a tour (a circuit meeting every node) → the edge set of such a circuit, cost Σ_{e∈T} c_e; reason: the cost of a tour depends only on its edge set
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, box "Held-Karp Bound", p. 255 (PDF p. 263)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_heldKarpBound
import Definitions.Def_CombOpt_HeldKarp_Graph_IsTour

namespace CombOpt.HeldKarp

/-- **The Held–Karp bound is a lower bound for the TSP (corrected: no loop when |V| = 1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, box
"Held-Karp Bound", p. 255 (PDF p. 263): "Let G = (V, E) be a graph with edge costs (c_e : e ∈ E),
let v_1 ∈ V, and for each node v ∈ V let y_v be a real number. Now for each edge e = uv ∈ E let
c̄_e = c_e − y_u − y_v and let C be the 1-tree bound for G with respect to the edge costs
(c̄_e : e ∈ E). Then 2Σ(y_v : v ∈ V) + C is a lower bound for the TSP on G (with respect to the
original edge costs (c_e : e ∈ E))."

For a finite graph `G`, real costs `c`, a node `v₁`, every `y : V → ℝ` and every tour `T` of `G`,
`2 Σ_v y_v + C ≤ Σ_{e ∈ T} c_e` (in `EReal`).

**Formalization Note.** Hypothesis `hG`: `G` has no loop, or at least two nodes. On one node with a
loop of cost 0 the loop is a tour of cost 0 while `C = ⊤`; the printed claim fails there and nowhere
else. -/
theorem heldKarpBound_le_tour {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : (∀ e : E, ¬ (G.ends e).IsDiag) ∨ 2 ≤ Fintype.card V)
    (c : E → ℝ) (v₁ : V) (y : V → ℝ) (T : Finset E) (hT : G.IsTour T) :
    G.heldKarpBound c v₁ y ≤ ((∑ e ∈ T, c e : ℝ) : EReal) := by sorry

end CombOpt.HeldKarp
