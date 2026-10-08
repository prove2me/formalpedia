-- Prove2me | Theorems.Thm_AryaANN_Search_disjoint_box_count
-- name    : AryaANN.Search.disjoint_box_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:47.868475+00:00
-- url     : https://prove2.me/theorems/612c0a31-3699-4a67-bdc7-3f0e595fcb76
-- title:
--   Proof of Lemma 4, p. 909 — at most ⌈1 + 6r/s⌉^d interior-disjoint boxes of side ≥ s/3 meet an open L_m ball of radius r
-- statement:
--   Fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$, a center $c\in\mathbb R^d$ and reals $r,s>0$. Let $B_1,\dots,B_N$ be boxes (axis-parallel rectangles of aspect ratio at most $3$) such that
--
--   1. every side of every $B_k$ has length at least $s/3$;
--   2. the interiors of the $B_k$ are pairwise disjoint;
--   3. every $B_k$ meets the open ball $\{x:\operatorname{dist}_m(c,x)<r\}$.
--
--   Then
--   $$N\le\Big\lceil 1+\frac{6r}{s}\Big\rceil^d.$$
--
--   This is the counting step of the proof of the packing constraint (Lemma 4): once the leaf cells meeting a ball are replaced by interior-disjoint boxes, the bound on their number follows from this statement.
--
--   **Formalization Note** The paper says the maximum number "is" $\lceil 1+6r/s\rceil^d$; only the upper bound is used later, and only it is stated. The ball is open, as in property (d) on p. 908: for a closed ball the count fails (five interior-disjoint rectangles of sides $\ge 1$ can touch a closed $L_\infty$ ball of radius $1/2$ in the plane, against the bound $4$).
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 909, proof of Lemma 4, first paragraph

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem disjoint_box_count {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (c : Fin d → ℝ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (N : ℕ) (B : Fin N → Rect d)
    (hbox : ∀ k, IsBox (B k))
    (hside : ∀ k i, s / 3 ≤ (B k).len i)
    (hdisj : Pairwise (fun k l => Disjoint (interior (B k).toSet) (interior (B l).toSet)))
    (hmeet : ∀ k, ((B k).toSet ∩ {x | lmDist m c x < r}).Nonempty) :
    N ≤ ⌈1 + 6 * r / s⌉₊ ^ d := by sorry

end AryaANN.Search
