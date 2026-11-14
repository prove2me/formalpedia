-- Prove2me | Theorems.Thm_DvorakNorin2018_cloud_supply_le_separator_charge
-- name    : DvorakNorin2018.cloud_supply_le_separator_charge
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T16:16:35.529267+00:00
-- url     : https://prove2.me/theorems/6646eae8-d8db-4d43-83bb-85f036c11cc8
-- title:
--   Observation 5, forward direction: cloud supply is bounded by separator charge
-- statement:
--   Let $G$ be a finite undirected graph, let $W$ be its designated sinks, and let $g(v)\in[0,1]$ and $f(u,v)\ge0$ describe a $W$-cloud. Flow is supported on graph edges, leaves no sink, and satisfies
--   $$g(v)+\sum_u f(u,v)=\sum_u f(v,u)\qquad(v\notin W).$$
--   Assume its congestion is at most $\alpha$, so $g(v)+\sum_u f(u,v)\le\alpha$ at every vertex. For every separation into pairwise disjoint parts $L,S,R$, with no edge between $L$ and $R$ and with $W\subseteq L\cup S$, the total supply satisfies
--   $$\sum_v g(v)\le |L|+\alpha|S|.$$
--
--   Equivalently, a cloud with supply greater than $s$ excludes every separator whose sink-side charge $|L|+\alpha|S|$ is at most $s$. This is the forward implication of Observation 5. The converse, constructing a cloud by max-flow/min-cut, is a separate result.
-- source:
--   Z. Dvorak and S. Norin, Treewidth of graphs with balanced separations, arXiv:1408.3869v2, https://arxiv.org/pdf/1408.3869v2, Section 2.2, Observation 5 (PDF pp. 4–5), forward implication. This is a foundation for the separator-to-treewidth step used by Ravichandran–Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Theorem 4.3 and Lemma 4.4.

import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false
open scoped Classical BigOperators

namespace DvorakNorin2018

open TreewidthApprox.Pushed

theorem cloud_supply_le_separator_charge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (supply : V → ℝ) (flow : V → V → ℝ) (α : ℝ)
    (hsupply : ∀ v, 0 ≤ supply v ∧ supply v ≤ 1)
    (hflow : ∀ u v, 0 ≤ flow u v)
    (hsupport : ∀ u v, ¬ G.Adj u v → flow u v = 0)
    (hsinks : ∀ u ∈ W, ∀ v, flow u v = 0)
    (hcons : ∀ v ∉ W, supply v + ∑ u, flow u v = ∑ u, flow v u)
    (hcongestion : ∀ v, supply v + ∑ u, flow u v ≤ α)
    (L S R : Finset V) (hpart : IsPartition3 Finset.univ L S R)
    (hno : NoEdge G L R) (hW : W ⊆ L ∪ S) :
    (∑ v, supply v) ≤ (L.card : ℝ) + α * S.card := by sorry

end DvorakNorin2018
