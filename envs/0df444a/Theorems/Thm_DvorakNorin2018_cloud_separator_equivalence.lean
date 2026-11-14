-- Prove2me | Theorems.Thm_DvorakNorin2018_cloud_separator_equivalence
-- name    : DvorakNorin2018.cloud_separator_equivalence
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:19:24.158934+00:00
-- url     : https://prove2.me/theorems/b0d4a957-ddb1-4eff-bc3a-20c21c203716
-- title:
--   Observation 5: bounded-congestion clouds and weighted separators
-- statement:
--   Let $G$ be a finite undirected graph, let $W$ be a designated set of sinks, and let $\alpha,s\ge0$. There exists a $W$-cloud with vertex supplies in $[0,1]$, congestion at most $\alpha$, and total supply greater than $s$ if and only if every separation into disjoint parts $L,S,R$ with no edge between $L$ and $R$ and $W\subseteq L\cup S$ satisfies $$s<|L|+\alpha|S|.$$
--
--   A cloud consists of nonnegative flows supported on graph edges, with no outgoing flow from sinks. Outside the sinks, incoming flow plus supply equals outgoing flow. Congestion is incoming flow plus supply at each vertex.
--
--   The theorem includes both implications, the finite-capacity split-network construction, application of max-flow/min-cut, and explicit decoding of the resulting network flow into the cloud. Nonnegative parameters include the source's strictly positive case. It is the full Observation 5 needed for the subsequent tame-cloud argument; it does not assert the later tameness or treewidth conclusions.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, Observation 5 (PDF pp. 4–5). The finite network chooses M=s+1 in place of infinite capacities.

import Definitions.Def_TreewidthApprox_Pushed_Setting
set_option autoImplicit false
open scoped Classical BigOperators

namespace DvorakNorin2018
open TreewidthApprox.Pushed
theorem cloud_separator_equivalence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (∃ (g : V → ℝ) (f : V → V → ℝ),
      (∀ v, 0 ≤ g v ∧ g v ≤ 1) ∧ (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ (∀ u ∈ W, ∀ v, f u v = 0) ∧
      (∀ v ∉ W, g v + ∑ u, f u v = ∑ u, f v u) ∧
      (∀ v, g v + ∑ u, f u v ≤ α) ∧ s < ∑ v, g v) ↔
    ∀ L S R : Finset V, IsPartition3 Finset.univ L S R → NoEdge G L R →
      W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card := by sorry
end DvorakNorin2018
