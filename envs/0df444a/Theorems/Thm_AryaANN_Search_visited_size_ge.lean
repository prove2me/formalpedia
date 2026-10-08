-- Prove2me | Theorems.Thm_AryaANN_Search_visited_size_ge
-- name    : AryaANN.Search.visited_size_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:56.885749+00:00
-- url     : https://prove2.me/theorems/0931166b-1f25-467f-8025-17c0c2cd45bd
-- title:
--   Proof of Lemma 5, p. 912 — every leaf cell visited before termination has size at least rε/d
-- statement:
--   Let $T$ be a valid BBD-tree with root cell a box $C$, fix an $L_m$ distance with $1\le m\le\infty$, $\varepsilon>0$ and a query point $q\in\mathbb R^d$. Let $E=((c_0,p_0),(c_1,p_1),\dots)$ list every leaf cell of $T$ exactly once, in nondecreasing order of distance from $q$, each with an associated point $p_j$ in the outer box of $c_j$. Let $N\ge1$ be the number of cells visited by the search before termination, and let
--   $$r=\operatorname{dist}_m(q,c_{N-1})$$
--   be the distance from $q$ to the last cell that did not cause termination. Then every visited cell is large:
--   $$\operatorname{size}(c_j)\ge\frac{r\varepsilon}{d}\qquad\text{for all } j<N.$$
--
--   Combined with the packing constraint (Lemma 4) applied to a ball of radius about $r$, this bounds the number of visited cells.
--
--   **Formalization Note** The search processes cell $j$ (compares its point) before testing whether to stop at $j$, and $N$ counts the cells processed before the one whose test fires, as in the paper's "last leaf cell that did not cause the algorithm to terminate". For $d=0$ the right-hand side is the junk value $r\varepsilon/0=0$, and the statement is trivially true there.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 912, proof of Lemma 5, first paragraph

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem visited_size_ge {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C, none⟩ T) (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves ⟨C, none⟩ T))
    (hpt : ∀ e ∈ E, e.2 ∈ e.1.outer.toSet)
    (hsorted : E.Pairwise (fun a b => cellDist m q a.1 ≤ cellDist m q b.1))
    (N : ℕ) (hN : IsVisitCount m ε q E N) (hN1 : 1 ≤ N) :
    ∀ j (hj : j < N),
      cellDist m q (E[N - 1]'(by have := hN.1; omega)).1 * ε / (d : ℝ)
        ≤ (E[j]'(by have := hN.1; omega)).1.size := by sorry

end AryaANN.Search
