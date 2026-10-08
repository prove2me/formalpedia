-- Prove2me | Theorems.Thm_AryaANN_Search_lemma_4
-- name    : AryaANN.Search.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:45.602993+00:00
-- url     : https://prove2.me/theorems/03c7ac12-0268-4d6b-872f-1ac3b95aa419
-- title:
--   Lemma 4 (Packing constraint), p. 908 — at most ⌈1 + 6r/s⌉^d leaf cells of size ≥ s meet an open L_m ball of radius r
-- statement:
--   Let $T$ be a valid BBD-tree whose root cell is a box $C$ with no inner box. Fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$, a center $c\in\mathbb R^d$ and reals $r>0$, $s>0$. Then the number of leaf cells of $T$ of size at least $s$ that intersect the ball $\{x:\operatorname{dist}_m(c,x)<r\}$ satisfies
--   $$\#\{\text{leaf cells } c' : \operatorname{size}(c')\ge s,\ c'\cap\mathcal B\ne\emptyset\}\le\Big\lceil 1+\frac{6r}{s}\Big\rceil^d.$$
--
--   This is property (d) of the subdivision with an explicit function of $r/s$ and $d$, independent of the number of data points. It is the geometric fact behind the bound on the number of cells the nearest neighbor search visits.
--
--   **Formalization Note** The ball is read as the open ball of property (d), p. 908, which the lemma establishes; the first step of the paper's proof fails for a closed ball. Leaf cells are counted by their position in the list of leaves. The data set plays no role in the claim and does not appear. The root may be any box rather than the paper's hypercube.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 908, Lemma 4 (Packing Constraint), with property (d)

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem lemma_4 {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C, none⟩ T) (c : Fin d → ℝ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    {j : Fin (leaves ⟨C, none⟩ T).length |
        s ≤ ((leaves ⟨C, none⟩ T).get j).size ∧
        (((leaves ⟨C, none⟩ T).get j).toSet ∩ {x | lmDist m c x < r}).Nonempty}.ncard
      ≤ ⌈1 + 6 * r / s⌉₊ ^ d := by sorry

end AryaANN.Search
