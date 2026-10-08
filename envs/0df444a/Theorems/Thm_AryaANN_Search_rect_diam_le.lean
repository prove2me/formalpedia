-- Prove2me | Theorems.Thm_AryaANN_Search_rect_diam_le
-- name    : AryaANN.Search.rect_diam_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:48.070145+00:00
-- url     : https://prove2.me/theorems/20fe6f3f-1f68-46b8-9c3f-d13b96cd44f3
-- title:
--   Proof of Lemma 5, p. 912 — the L_m diameter of a rectangle is at most d times (indeed d^{1/m} times) its longest side
-- statement:
--   Fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$ and a rectangle $R$ whose longest side has length $\operatorname{size}(R)$. For all $x,y\in R$,
--   $$\operatorname{dist}_m(x,y)\le d\cdot\operatorname{size}(R),$$
--   and, when $m$ is finite, $\operatorname{dist}_m(x,y)\le d^{1/m}\operatorname{size}(R)$.
--
--   In the proof of Lemma 5 this bounds the distance between a point of a visited cell and the data point associated with it, both of which lie in the cell's outer box.
--
--   **Formalization Note** The paper speaks of "this cell"; the bound is stated for rectangles, which covers the outer box of a cell and hence the cell and its associated data point.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 912, proof of Lemma 5, first paragraph

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem rect_diam_le {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (R : Rect d) :
    ∀ x ∈ R.toSet, ∀ y ∈ R.toSet,
      lmDist m x y ≤ (d : ℝ) * R.size ∧
      (m ≠ ⊤ → lmDist m x y ≤ (d : ℝ) ^ ((1 : ℝ) / m.toNat) * R.size) := by sorry

end AryaANN.Search
