-- Prove2me | Theorems.Thm_CombOpt_MinCut_lemma_3_37
-- name    : CombOpt.MinCut.lemma_3_37
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:44.74843+00:00
-- url     : https://prove2.me/theorems/849624ca-8f53-4f65-b477-ba40118e5044
-- title:
--   Lemma 3.37 — $\lambda(G;p,q)\ge\min(\lambda(G;r,q),\lambda(G;p,r))$
-- statement:
--   Let $G=(V,E)$ be a finite capacitated multigraph and let $\lambda(G;a,b)$ denote the capacity of a minimum $(a,b)$-cut. For all nodes $p,q,r\in V$,
--
--   $$\lambda(G;p,q)\ \ge\ \min\bigl(\lambda(G;r,q),\ \lambda(G;p,r)\bigr).$$
--
--   This triangle inequality reduces the proof of Theorem 3.36, in the case where the last two nodes of the legal ordering are not adjacent, to two bounds involving the third-to-last node.
--
--   Differences from the source:
--   - generalization: capacities $u_e>0$ and $G$ connected (setting of §3.5, p. 72) → arbitrary real capacities and any finite multigraph; reason: a minimum $(p,q)$-cut is a $(r,q)$-cut or a $(p,r)$-cut whatever the capacities; the book's case is an instance.
--   - encoding: $\lambda(G;a,b)$ real → values in $\mathbb R\cup\{+\infty\}$ with $\lambda(G;a,a)=+\infty$; reason: makes the statement meaningful for coinciding $p,q,r$, which the book's "If $p,q,r\in V$" does not exclude; for distinct nodes the values are the book's.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 3.37, p. 75 (PDF p. 84)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_minCutValue

namespace CombOpt.MinCut

/-- **Lemma 3.37 (triangle inequality for minimum cuts).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 3.37,
p. 75 (PDF p. 84): "If p, q, r ∈ V, then λ(G; p, q) ≥ min(λ(G; r, q), λ(G; p, r))."

For any three nodes `p, q, r` of a finite multigraph `G` with capacities `u`,
`λ(G; p, q) ≥ min(λ(G; r, q), λ(G; p, r))`.

**Formalization Note.** `λ(G; ·, ·)` lies in `WithTop ℝ` and equals `⊤` for two equal nodes, so the
statement covers coinciding `p, q, r` without a side condition. The capacities are arbitrary
reals. -/
theorem lemma_3_37 {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E) (p q r : V) :
    min (G.minCutValue r q) (G.minCutValue p r) ≤ G.minCutValue p q := by sorry

end CombOpt.MinCut
