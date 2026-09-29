-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_cutrk_submodular
-- name    : ApproxCliqueWidth.Certificate.cutrk_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:34:04.496983+00:00
-- url     : https://prove2.me/theorems/42fcdfea-2ef8-4f40-96c1-a4fa92ddf6b9
-- title:
--   Corollary 6.2 — $\mathrm{cutrk}^*_G$ and $\mathrm{cutrk}_G$ are submodular
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$. If $(X_1, Y_1)$ and $(X_2, Y_2)$ are pairs of disjoint subsets of $V$, then
--   $$\mathrm{cutrk}^*_G(X_1, Y_1) + \mathrm{cutrk}^*_G(X_2, Y_2) \ge \mathrm{cutrk}^*_G(X_1 \cap X_2, Y_1 \cup Y_2) + \mathrm{cutrk}^*_G(X_1 \cup X_2, Y_1 \cap Y_2).$$
--   Moreover, for all $X_1, X_2 \subseteq V$,
--   $$\mathrm{cutrk}_G(X_1) + \mathrm{cutrk}_G(X_2) \ge \mathrm{cutrk}_G(X_1 \cap X_2) + \mathrm{cutrk}_G(X_1 \cup X_2).$$
--
--   Submodularity of cut-rank is what makes rank-width a branch-width of a symmetric submodular function, so that the results of Section 5 apply to graphs.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 522, Corollary 6.2

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Corollary 6.2 (p. 522): submodularity of `cutrk*_G` on disjoint pairs and of
`cutrk_G`. -/
theorem cutrk_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ X₁ Y₁ X₂ Y₂ : Finset V, Disjoint X₁ Y₁ → Disjoint X₂ Y₂ →
        cutrkStar G (X₁ ∩ X₂) (Y₁ ∪ Y₂) + cutrkStar G (X₁ ∪ X₂) (Y₁ ∩ Y₂) ≤
          cutrkStar G X₁ Y₁ + cutrkStar G X₂ Y₂) ∧
    IsSubmodular (cutrk G) := by sorry

end ApproxCliqueWidth.Certificate
