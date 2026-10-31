-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_forest_polytope
-- name    : CombOpt.HeldKarp.forest_polytope
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:40.130627+00:00
-- url     : https://prove2.me/theorems/c776d601-fc92-4130-87e8-35d93f11f250
-- title:
--   Theorem 8.8: the forest polytope
-- statement:
--   Let $G=(V,E)$ be a finite graph (loops and parallel edges allowed). For $F\subseteq E$ let $\chi^F\in\mathbb R^E$ be its characteristic vector ($\chi^F_e=1$ if $e\in F$, $0$ otherwise). Then the convex hull of the characteristic vectors of the forests of $G$ is the set of all $x\in\mathbb R^E$ satisfying
--   $$x(\gamma(T))\le |T|-1\quad\text{for all } T,\ \emptyset\subset T\subseteq V,\qquad(8.5)$$
--   $$x_e\ge 0\quad\text{for all } e\in E.$$
--
--   This is Edmonds' description of the forest polytope, the polyhedral input behind the 1-tree linear program (7.7) and the spanning-tree polytope.
--
--   Differences from the source:
--   - encoding: forests of G (subgraphs without circuits) → edge sets F ⊆ E containing no circuit; reason: a characteristic vector depends only on the edge set; (V, F) is a forest exactly when no circuit has all its edges in F
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.8, p. 280 (PDF p. 287)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsForest
import Definitions.Def_CombOpt_HeldKarp_Graph_gamma

namespace CombOpt.HeldKarp

/-- **Theorem 8.8: the forest polytope.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 8.8,
p. 280 (PDF p. 287): "Let G = (V, E) be a graph. The convex hull of characteristic vectors of forests
of G is the set of all x satisfying x(γ(T)) ≤ |T| − 1, for all T, ∅ ⊂ T ⊆ V (8.5); x_e ≥ 0, for all
e ∈ E."

For a finite graph `G` (loops and parallel edges allowed), the convex hull in `ℝ^E` of the vectors
`χ^F` (`χ^F_e = 1` if `e ∈ F`, else `0`) over all forests `F` equals
`{x | x(γ(T)) ≤ |T| − 1 for every nonempty T ⊆ V, and x ≥ 0}`.

**Formalization Note.** A forest is recorded by its edge set (`Graph.IsForest`); `|T| − 1` is
computed in `ℝ`. -/
theorem forest_polytope {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Graph V E) :
    convexHull ℝ {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0} =
      {x : E → ℝ | (∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) ∧
        ∀ e : E, 0 ≤ x e} := by sorry

end CombOpt.HeldKarp
