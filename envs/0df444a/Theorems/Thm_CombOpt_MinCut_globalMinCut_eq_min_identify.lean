-- Prove2me | Theorems.Thm_CombOpt_MinCut_globalMinCut_eq_min_identify
-- name    : CombOpt.MinCut.globalMinCut_eq_min_identify
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:49.942054+00:00
-- url     : https://prove2.me/theorems/38f67f88-09db-47f1-aa59-38de08dff1e6
-- title:
--   §3.5.1 — $\lambda(G)=\min(\lambda(G_{vw}),\lambda(G;v,w))$
-- statement:
--   Let $G=(V,E)$ be a finite capacitated multigraph and $v,w$ distinct nodes. Write $\lambda(G)$ for the capacity of a minimum cut $\delta(S)$, $\emptyset\ne S\ne V$, $\lambda(G;v,w)$ for the capacity of a minimum $(v,w)$-cut, and $G_{vw}$ for the graph obtained by identifying $v$ with $w$. Then
--
--   $$\lambda(G)=\min\bigl(\lambda(G_{vw}),\ \lambda(G;v,w)\bigr).$$
--
--   This identity justifies the node identification algorithm: a minimum cut of $G$ is either a minimum $(v,w)$-cut or survives as a minimum cut of $G_{vw}$, so the problem reduces to one $(v,w)$-cut computation and a graph with one node fewer.
--
--   Differences from the source:
--   - generalization: capacities $u_e>0$ and $G$ connected (the setting of the minimum cut problem, p. 72) → arbitrary real capacities and any finite multigraph; reason: the identity splits the minimum over $\emptyset\ne S\ne V$ into the sets separating $v,w$ and those that do not, which needs no sign or connectivity; the book's case is an instance.
--   - encoding: real optimal values → values in $\mathbb R\cup\{+\infty\}$ with $\min\emptyset=+\infty$; reason: when $|V|=2$, $G_{vw}$ has a single node and no cut with $\emptyset\ne S\ne V(G_{vw})$, so $\lambda(G_{vw})=+\infty$ and the identity reads $\lambda(G)=\lambda(G;v,w)$; for $|V|\ge3$ all three values are real.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5.1 (Node Identification Algorithm), p. 74 (PDF p. 83)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_identify
import Definitions.Def_CombOpt_MinCut_CapGraph_minCutValue
import Definitions.Def_CombOpt_MinCut_CapGraph_globalMinCut

namespace CombOpt.MinCut

open Classical in
/-- **λ(G) = min(λ(G_vw), λ(G; v, w)).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5.1
(Node Identification Algorithm), p. 74 (PDF p. 83): "It follows from the observations above that
λ(G) = min(λ(G_vw), λ(G; v, w))."

For distinct nodes `v, w` of a finite multigraph `G` with capacities `u`, the minimum capacity of
a cut `δ(S)`, `∅ ≠ S ≠ V`, equals the smaller of the minimum cut capacity of `G_vw` and the minimum
capacity of a `(v, w)`-cut of `G`.

**Formalization Note.** All three values lie in `WithTop ℝ` with `min ∅ = ⊤`. When `G` has exactly
two nodes, `G_vw` has one node and no cut `δ(S)` with `∅ ≠ S ≠ V(G_vw)`, so `λ(G_vw) = ⊤` and the
identity reads `λ(G) = λ(G; v, w)`. The capacities are arbitrary reals. -/
theorem globalMinCut_eq_min_identify {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E)
    (v w : V) (hvw : v ≠ w) :
    G.globalMinCut = min (G.identify v w).globalMinCut (G.minCutValue v w) := by sorry

end CombOpt.MinCut
