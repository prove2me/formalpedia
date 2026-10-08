-- Prove2me | Theorems.Thm_AryaANN_Search_replacement
-- name    : AryaANN.Search.replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:02.258115+00:00
-- url     : https://prove2.me/theorems/a361b5dd-a9f4-4174-8c77-4a29de26f26d
-- title:
--   Proof of Lemma 4, p. 909 — the leaf cells of size ≥ s meeting a ball can be replaced by as many interior-disjoint boxes of size ≥ s meeting it
-- statement:
--   Let $T$ be a valid BBD-tree whose root cell is a box $C$ with no inner box, fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$, a center $c$ and reals $r,s>0$, and let $\mathcal B=\{x:\operatorname{dist}_m(c,x)<r\}$ be the open ball. Let $J$ be the set of leaf cells of $T$ of size at least $s$ that meet $\mathcal B$. Then there are boxes $(B_j)_{j\in J}$, one for each such leaf cell, such that
--
--   1. each $B_j$ is a box (aspect ratio at most $3$), has size at least $s$, and meets $\mathcal B$;
--   2. the interiors of the $B_j$ are pairwise disjoint.
--
--   The boxes need not be cells of the subdivision. Together with the counting step for interior-disjoint boxes, this yields the packing constraint (Lemma 4); it is where stickiness and the hierarchy of the tree enter.
--
--   **Formalization Note** "An equal number of" boxes is expressed by indexing the boxes by the set $J$ of leaf positions itself. "Boxes" are rectangles of aspect ratio at most $3$, so a box of size at least $s$ has every side at least $s/3$. The ball is open, as in property (d), p. 908.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 909, proof of Lemma 4, second paragraph

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem replacement {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C, none⟩ T) (c : Fin d → ℝ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ∃ B : {j : Fin (leaves ⟨C, none⟩ T).length //
          s ≤ ((leaves ⟨C, none⟩ T).get j).size ∧
          (((leaves ⟨C, none⟩ T).get j).toSet ∩ {x | lmDist m c x < r}).Nonempty} → Rect d,
      (∀ j, IsBox (B j) ∧ s ≤ (B j).size ∧ ((B j).toSet ∩ {x | lmDist m c x < r}).Nonempty) ∧
      Pairwise (fun j k => Disjoint (interior (B j).toSet) (interior (B k).toSet)) := by sorry

end AryaANN.Search
