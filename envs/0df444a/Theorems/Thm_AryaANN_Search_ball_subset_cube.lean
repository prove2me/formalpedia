-- Prove2me | Theorems.Thm_AryaANN_Search_ball_subset_cube
-- name    : AryaANN.Search.ball_subset_cube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:58.906486+00:00
-- url     : https://prove2.me/theorems/a4027a49-c587-429d-baeb-64ab262ccf4c
-- title:
--   Proof of Lemma 4, p. 909 — an L_m ball of radius r lies in the axis-aligned hypercube of side 2r around its center
-- statement:
--   Fix an $L_m$ distance on $\mathbb R^d$ with $1\le m\le\infty$, a center $c\in\mathbb R^d$ and a real $r$. Every point of the closed ball of radius $r$ about $c$ lies in the hypercube $\prod_i[c_i-r,c_i+r]$ of side $2r$:
--   $$\operatorname{dist}_m(c,x)\le r\ \Longrightarrow\ |x_i-c_i|\le r\quad\text{for all } i.$$
--
--   This reduces counting boxes that meet an $L_m$ ball to counting boxes that meet a cube, which is the shape used in the packing argument for Lemma 4.
--
--   **Formalization Note** The statement is given for the closed ball, which contains the open one.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), p. 909, proof of Lemma 4, first paragraph

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

theorem ball_subset_cube {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (c : Fin d → ℝ) (r : ℝ) :
    ∀ x : Fin d → ℝ, lmDist m c x ≤ r → ∀ i, |x i - c i| ≤ r := by sorry

end AryaANN.Search
