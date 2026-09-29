-- Prove2me | Theorems.Thm_ChvatalPolytopes_Separation_no_clique_cutset_of_alpha_critical
-- name    : ChvatalPolytopes.Separation.no_clique_cutset_of_alpha_critical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:19:39.521884+00:00
-- url     : https://prove2.me/theorems/22f3e31c-8bb4-48bb-baae-542fe22c0570
-- title:
--   Corollary 4.3 — no complete subgraph of a connected $\alpha$-critical graph is a cutset
-- statement:
--   Let $G=(V,E)$ be a finite connected graph that is $\alpha$-critical, i.e. $\alpha(G-e)=\alpha(G)+1$ for every edge $e$. Let $K\subseteq V$ induce a complete subgraph of $G$ (any complete vertex set, not necessarily a maximal clique, possibly empty). Then $K$ is not a cutset of $G$:
--   $$\text{any two vertices } x,y\notin K \text{ are joined by a path of } G-K.$$
--
--   This is a result of Berge on the structure of $\alpha$-critical graphs, obtained in the paper as a consequence of the two polyhedral Theorems 4.1 and 4.2: gluing along a clique produces no new facets, while in a connected $\alpha$-critical graph the inequality $\sum_u x_u\le\alpha(G)$ must be a facet.
--
--   **Formalization Note** $K$ is a `Set V` with `G.IsClique K`. "Cutset" is the mission's `IsCutset`: two vertices outside $K$ with no path between them in the subgraph induced on $V\setminus K$. This is the reading the paper's proof uses ($G=G_1\cup G_2$ with $V_1\cap V_2=K$ complete and $V_1-V_2$, $V_2-V_1$ nonempty); it does not count $K=V$ as a cutset, so the statement is not falsified by $K_1$ or $K_2$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 144, Corollary 4.3 (Berge [3, Corollary 2, Chapter 13, Section 3])

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ChvatalPolytopes_Separation_IsCutset

namespace ChvatalPolytopes.Separation

/-- **Corollary 4.3** (Chvátal 1975, p. 144; Berge [3, Corollary 2, Chapter 13, Section 3]).
No complete subgraph of a connected α-critical graph is a cutset.

`K` is any complete vertex set (`G.IsClique K`, not necessarily maximal, possibly empty);
"cutset" is `IsCutset`: two vertices outside `K` not joined by any path of `G − K`. -/
theorem no_clique_cutset_of_alpha_critical {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hcrit : IsAlphaCritical G)
    (K : Set V) (hK : G.IsClique K) :
    ¬ IsCutset G K := by sorry

end ChvatalPolytopes.Separation
