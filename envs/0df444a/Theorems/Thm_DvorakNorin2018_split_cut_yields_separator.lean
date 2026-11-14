-- Prove2me | Theorems.Thm_DvorakNorin2018_split_cut_yields_separator
-- name    : DvorakNorin2018.split_cut_yields_separator
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T17:07:53.247282+00:00
-- url     : https://prove2.me/theorems/e9228021-f8ab-4ad6-b63e-51e8129a9c9e
-- title:
--   Observation 5: a split-network cut yields a separator of no greater charge
-- statement:
--   Let $G$ be finite with sinks $W$. In the split-vertex network with nonnegative vertex capacity $\alpha$ and nonnegative large-arc capacity $M$, suppose a source/sink cut $C$ has capacity at most $s<M$. Then $G$ admits a separation into disjoint parts $L,S,R$, with no edge from $L$ to $R$, such that $$W\subseteq L\cup S,\qquad |L|+\alpha|S|\le s.$$ This proves the cut-conversion step of the max-flow reduction in Observation 5. It does not yet assert extraction of a cloud from a network flow.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, network construction preceding Observation 5. The finite-capacity version uses M>s.

import Definitions.Def_DvorakNorin2018_SplitNetwork
set_option autoImplicit false
open scoped Classical BigOperators

namespace DvorakNorin2018
open TreewidthApprox.Pushed StableMSR.Recovery.SplitNetwork
theorem split_cut_yields_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M s : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hMs : s < M) (C : Finset (Node V)) (hsource : source ∈ C) (hsink : sink ∉ C)
    (hcut : cut G W α M C ≤ s) :
    ∃ L S R : Finset V, IsPartition3 Finset.univ L S R ∧ NoEdge G L R ∧
      W ⊆ L ∪ S ∧ (L.card : ℝ) + α * S.card ≤ s := by sorry
end DvorakNorin2018
