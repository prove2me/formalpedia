-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_theorem_5
-- name    : CapacitatedKMedianFPT.Main.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:02.962509+00:00
-- url     : https://prove2.me/theorems/9c2b21c9-3ccb-4ef9-8338-2dd5113e20a4
-- title:
--   Theorem 5 — the maximum-weight matching value is submodular in the right vertex set
-- statement:
--   Let $G$ be an edge-weighted bipartite graph with vertex sets $L$ and $R$ on the two sides. For $X\subseteq R$, let $u(X)$ be the maximum weight of a matching that can only match the vertices in $X$ on the right side. Then $u$ is a submodular function of $X$:
--   $$u(A)+u(B)\ge u(A\cup B)+u(A\cap B)\qquad\text{for all }A,B\subseteq R.$$
--
--   This is Shapley's theorem on the optimal assignment problem; it gives the submodularity of the savings function (Lemma 5).
--
--   **Formalization Note** $L$ and $R$ are finite; edge weights may have any sign, as in the source's statement.
--
--   Differences from the source:
--
--   - encoding: an edge-weighted bipartite graph G → an edge relation E ⊆ L × R with weights w : L × R → ℝ on finite L, R; matchings as partial maps injective on matched vertices; reason: the same graphs and matchings
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 13, Theorem 5 ([Sha62], [BNR17, Lemma 2])

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Matching
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Theorem 5** ([Sha62], [BNR17, Lemma 2]) (p. 13). For a finite edge-weighted bipartite graph
with sides `L` and `R` (edge relation `E`, weights `w` of any sign), the maximum weight `u(X)` of a
matching that matches only right vertices in `X ⊆ R` is a submodular function of `X`. -/
theorem theorem_5 {L R : Type} [Fintype L] [Fintype R] [DecidableEq R]
    (E : L → R → Prop) (w : L → R → ℝ) :
    NonmonotoneSubmod.Shared.Submodular (maxMatchingWeight E w) := by sorry

end CapacitatedKMedianFPT.Main
