-- Prove2me | Theorems.Thm_AryaANN_Search_lemma_5
-- name    : AryaANN.Search.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:47.26472+00:00
-- url     : https://prove2.me/theorems/212919b4-d13c-473f-a2c8-8e11b6c6ac00
-- title:
--   Lemma 5, p. 911 — the nearest neighbor search on a BBD-tree visits at most ⌈1 + 6d/ε⌉^d leaf cells, for any Minkowski metric
-- statement:
--   Let $T$ be a valid BBD-tree whose root cell is a box $C$ with no inner box, fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$ ("any Minkowski metric"), an approximation parameter $\varepsilon>0$ and a query point $q\in\mathbb R^d$. Let $E=((c_0,p_0),(c_1,p_1),\dots)$ be an enumeration of the leaf cells of $T$ such that
--
--   1. every leaf cell occurs exactly once;
--   2. the cells occur in nondecreasing order of distance from $q$ (ties in any order);
--   3. the data point $p_j$ associated with $c_j$ lies in the outer box of $c_j$.
--
--   The search processes $c_0,c_1,\dots$ in turn, keeping the closest point $p$ seen so far, and terminates at the first cell whose distance from $q$ exceeds $\operatorname{dist}_m(q,p)/(1+\varepsilon)$. The number $N$ of cells visited up until termination, that is, the cells preceding the terminating cell, satisfies
--   $$N\le\Big\lceil 1+\frac{6d}{\varepsilon}\Big\rceil^d.$$
--
--   The bound does not depend on the number of data points. Multiplied by the $O(\log n)$ cost of enumerating each cell, it gives the query time of Theorem 1(i).
--
--   **Formalization Note** The paper's $C_{d,\varepsilon}$ is a name for the number of visited cells; the formal conclusion is the explicit bound. A cell is processed (its point compared) before its own termination test, and $N$ counts the cells processed before the one whose test fires, or all of them if none fires. This is the count bounded in the paper's proof, where $r$ is the distance to "the last leaf cell that did *not* cause the algorithm to terminate" (p. 912). The printed statement says "the number of leaf cells visited"; if the firing cell is also counted, a valid one-dimensional tree with $\varepsilon=6$ needs three processed cells against the bound $2$, so the formal statement follows the proof's count (the discrepancy is recorded in `HARD.md`). The enumeration is a permutation of the leaf cells sorted by distance, the abstract output of property (e); the associated point lies in the cell's outer box, as in properties (a)–(b). The tree is any tree satisfying the §2.1 invariants, with any box as root. Theorem 1's $O(\cdot)$ time and space claims are not formalized.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 911, Lemma 5 (with the search of §4, p. 911, and its proof, p. 912)

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

/-- Lemma 5 (p. 911): the number `N` of leaf cells the search visits up until termination is at
most `⌈1 + 6d/ε⌉^d`. As in the proof (p. 912), `N` counts the cells that did not cause termination;
the cell whose test fires is not counted (counting it, the printed bound can be exceeded by one). -/
theorem lemma_5 {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C, none⟩ T) (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves ⟨C, none⟩ T))
    (hpt : ∀ e ∈ E, e.2 ∈ e.1.outer.toSet)
    (hsorted : E.Pairwise (fun a b => cellDist m q a.1 ≤ cellDist m q b.1))
    (N : ℕ) (hN : IsVisitCount m ε q E N) :
    N ≤ ⌈1 + 6 * (d : ℝ) / ε⌉₊ ^ d := by sorry

end AryaANN.Search
