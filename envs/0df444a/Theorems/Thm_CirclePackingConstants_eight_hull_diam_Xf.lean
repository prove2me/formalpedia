-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xf
-- name    : CirclePackingConstants.eight_hull_diam_Xf
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T08:49:24.230985+00:00
-- url     : https://prove2.me/theorems/8d9aed21-83b7-462e-b7be-6807f755b3f1
-- title:
--   Diameter of a Schaer–Meir polygon (Xf) is at most $d_8$
-- statement:
--   Use Cartesian coordinates $(u,v)$ whose origin is the centre $C$ of the unit square, so that the square is $[-\tfrac12,\tfrac12]^2$, and put $s=(2-\sqrt3)/2$ and $d_8=\sqrt{2-\sqrt3}$. Let $P$ be the convex hull of the 6 points
--
--   $$
--   V_1=\big(-1+\tfrac{1}{2}\sqrt3,\,1-\tfrac{1}{2}\sqrt3\big), V_2=\big(0,\,-1+\tfrac{1}{2}\sqrt3\big), V_3=\big(\tfrac{1}{2}-\tfrac{1}{4}\sqrt3,\,-\tfrac{1}{4}\big), V_4=\big(1-\tfrac{1}{2}\sqrt3,\,-1+\tfrac{1}{2}\sqrt3\big), V_5=\big(0,\,1-\tfrac{1}{2}\sqrt3\big), V_6=\big(-\tfrac{1}{2}+\tfrac{1}{4}\sqrt3,\,\tfrac{1}{4}\big).
--   $$
--
--   This is the convex hull of the vertices of the polygon $R_2H_2CN_4R_4H_4N_2$ of the last step of the proof of Proposition 3 of Schaer and Meir (Figure 3). Then any two points $p,q\in P$ satisfy
--
--   $$
--   |p-q|^2\le 2-\sqrt3 ,\qquad\text{i.e. }\ |p-q|\le d_8 .
--   $$
--
--   This is the instance of the Lemma of Schaer and Meir (a convex polygon whose vertices are pairwise at distance at most $d_8$ has diameter at most $d_8$) used in their proof that eight points of the unit square cannot be pairwise more than $d_8$ apart; all pairwise vertex distances are at most $d_8$, with equality for some pairs.
--
--   **Formalization Note.** Points are elements of `ℝ × ℝ`, `sqDist` is the squared Euclidean distance, and the polygon is `convexHull ℝ` of the finite vertex set.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Figure 3, the Lemma and the proof of Proposition 3.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem eight_hull_diam_Xf :
    ∀ p ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * Real.sqrt 3), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3), ((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * Real.sqrt 3), ((1:ℝ)/4))} : Set Point), ∀ q ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * Real.sqrt 3), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3), ((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * Real.sqrt 3), ((1:ℝ)/4))} : Set Point),
      sqDist p q ≤ 2 - Real.sqrt 3 := by sorry
