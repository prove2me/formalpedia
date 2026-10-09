-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_lemma_13
-- name    : ExpanderBIS.Potts.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:13.196977+00:00
-- url     : https://prove2.me/theorems/0352515a-9fb0-4307-a5eb-bf27fd5230a9
-- title:
--   Lemma 13 — the polymer sum approximates one dominant-color sector
-- statement:
--   Let $G$ be a nonempty finite $\alpha$-expander, with $\alpha>0$ and $q\ge2$ colors. Fix a color $r\in[q]$. If $\beta>2\log(eq)/\alpha$, then the polymer expression $\widetilde Z_G(\beta)=e^{\beta e(G)}\Xi(G)$ is an $e^{-n}$-relative approximation to $Z_G^r(\beta)$, where $n=|V(G)|$ and $e(G)$ is the number of edges:
--
--   $$
--   e^{-e^{-n}}\widetilde Z_G(\beta)\le Z_G^r(\beta)
--   \le e^{e^{-n}}\widetilde Z_G(\beta).
--   $$
--
--   This connects the partition sum near a specified monochromatic ground state to the polymer partition sum.
--
--   **Formalization Note** The graph has at least one vertex. $Z_G^r$ uses a strict majority of color $r$, while polymers have size at most half the graph, as on the page.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 14, Lemma 13

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- Lemma 13, p. 14. -/
theorem lemma_13 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (q : ℕ) (r : Fin q)
    (hα : 0 < α) (hq : 2 ≤ q) (hG : IsExpander G α)
    (hβ : 2 * Real.log (Real.exp 1 * (q : ℝ)) / α < β) :
    IsRelApprox (Real.exp (-(Fintype.card V : ℝ)))
      (Real.exp (β * (#G.edgeFinset : ℝ)) * polymerXi G q β)
      (pottsZj G q β r) := by sorry

end ExpanderBIS.Potts
