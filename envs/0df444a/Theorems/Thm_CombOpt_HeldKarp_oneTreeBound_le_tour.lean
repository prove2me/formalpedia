-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_oneTreeBound_le_tour
-- name    : CombOpt.HeldKarp.oneTreeBound_le_tour
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:31.543121+00:00
-- url     : https://prove2.me/theorems/3249d639-f5db-4dfe-8199-dfb191d6e176
-- title:
--   1-tree Bound (p. 253): $A+B$ is a lower bound for the TSP (corrected: no loop on one node)
-- statement:
--   Let $G=(V,E)$ be a finite graph with real edge costs $c$, and let $v_1\in V$. Let
--   $$A=\min\{c_e+c_f : e,f\in\delta(v_1),\ e\ne f\}$$
--   and let $B$ be the cost of a minimum spanning tree of $G\setminus v_1$. Assume $G$ has no loop or has at least two nodes. Then for every tour $T$ of $G$,
--   $$A+B\le \sum_{e\in T}c_e .$$
--
--   This is the 1-tree lower bound for the traveling salesman problem.
--
--   Differences from the source:
--   - correction: any graph G → G has no loop, or |V| ≥ 2; reason: counterexample: one node v_1 with a loop of cost 0; the loop is a tour (circuit of length 1 meeting every node) of cost 0, but δ(v_1) = ∅ so A = +∞ and the bound is +∞
--   - encoding: minima A, B (and the bound) over possibly empty sets → infima in EReal, +∞ on an empty set; reason: Lean convention; on every instance where the book's minima exist they are the same values, and +∞ is the natural value of an empty minimum
--   - encoding: spanning tree of the graph G \ v_1 → edge set of G avoiding v_1, connecting all nodes ≠ v_1 by paths in it, with no circuit; reason: G \ v_1 has the nodes V \ {v_1} and the edges of G not incident with v_1, so these are the same edge sets
--   - encoding: a tour (a circuit meeting every node) → the edge set of such a circuit, cost Σ_{e∈T} c_e; reason: the cost of a tour depends only on its edge set
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, box "1-tree Bound", p. 253 (PDF p. 261)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeBound
import Definitions.Def_CombOpt_HeldKarp_Graph_IsTour

namespace CombOpt.HeldKarp

/-- **The 1-tree bound is a lower bound for the TSP (corrected: no loop when |V| = 1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, box
"1-tree Bound", p. 253 (PDF p. 261): "Let G = (V, E) with edge costs (c_e : e ∈ E) and let v_1 ∈ V.
Now let A = min{c_e + c_f : e, f ∈ δ(v_1), e ≠ f} and let B be the cost of a minimum spanning tree
in G \ v_1. Then A + B is a lower bound for the TSP on G."

For a finite graph `G`, real edge costs `c`, a node `v₁` and every tour `T` of `G`,
`A + B ≤ Σ_{e ∈ T} c_e` (in `EReal`).

**Formalization Note.** Hypothesis `hG`: `G` has no loop, or at least two nodes. On one node with a
loop of cost 0 the loop is a tour (a circuit of length 1 meeting every node) of cost 0, while
`δ(v₁) = ∅` gives `A = ⊤`; the printed claim fails there and nowhere else. -/
theorem oneTreeBound_le_tour {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : (∀ e : E, ¬ (G.ends e).IsDiag) ∨ 2 ≤ Fintype.card V)
    (c : E → ℝ) (v₁ : V) (T : Finset E) (hT : G.IsTour T) :
    G.oneTreeBound c v₁ ≤ ((∑ e ∈ T, c e : ℝ) : EReal) := by sorry

end CombOpt.HeldKarp
