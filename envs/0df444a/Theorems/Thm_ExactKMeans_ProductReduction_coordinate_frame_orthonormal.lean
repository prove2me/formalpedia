-- Prove2me | Theorems.Thm_ExactKMeans_ProductReduction_coordinate_frame_orthonormal
-- name    : ExactKMeans.ProductReduction.coordinate_frame_orthonormal
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T19:16:32.623477+00:00
-- url     : https://prove2.me/theorems/9feb4dce-2b17-4e4d-a9d6-4f70837287bc
-- title:
--   Orthonormality of the coordinate planes of the selector construction
-- statement:
--   Let $a,b\ge1$ with $ab\ge2$ and odd $t\ge3$ be the Section 5 parameters, and work in $\mathbb R^{2b+1}$. The selector lives in the coordinate planes $\operatorname{span}(e_j,e_j^\perp)$, $j=1,\dots,b$, which occupy the first $2b$ coordinates, and the last coordinate direction is the axis $\hat e$ along which the selectors are placed.
--
--   1. The vectors $e_1,\dots,e_b,e_1^\perp,\dots,e_b^\perp$ form an orthonormal family: $\langle e_j,e_k\rangle=\langle e_j^\perp,e_k^\perp\rangle=[j=k]$ and $\langle e_j,e_k^\perp\rangle=0$.
--   2. Each $e_j$ and each $e_j^\perp$ is orthogonal to the axis, and $\hat e$ is a unit vector.
--   3. For all real coefficients $x_1,\dots,x_b$ and $y_1,\dots,y_b$,
--
--   $$
--   \Big\|\sum_{j=1}^{b}\big(x_j\,e_j+y_j\,e_j^\perp\big)\Big\|^2=\sum_{j=1}^{b}\big(x_j^2+y_j^2\big).
--   $$
--
--   These are the basic facts about the ambient coordinate system of the construction. Every selector point, the averaged vector $\bar e=\frac1{\sqrt b}\sum_j e_j$, and the reference displacement $\hat\mu(s)=\frac{r}{\sqrt b}\sum_j e_j(s_j)$ are combinations of this form, so norms of means and cluster costs reduce to sums of squares of coefficients.
--
--   **Formalization Note** In the published definitions, $e_j$, $e_j^\perp$ and $\hat e$ are the standard unit vectors of $\mathbb R^{2b+1}$ in coordinates $2j$, $2j+1$ and $2b$ (zero-based, $j<b$), and $[j=k]$ denotes the Kronecker delta.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 28–31 (PDF 29–32), Definitions 3–4: the b orthogonal coordinate planes with basis vectors e_j, e_j^⊥ and their normalized averages; used in the proof of Lemma 14, printed p. 31

import Definitions.Def_ExactKMeans_ProductReduction_Selector

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace ExactKMeans.ProductReduction

theorem coordinate_frame_orthonormal (p : Parameters) :
    (∀ j k : Fin p.b, inner ℝ (e p j) (e p k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (ep p j) (ep p k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (e p j) (ep p k) = 0) ∧
    (∀ j : Fin p.b, inner ℝ (e p j) (axis p) = 0 ∧ inner ℝ (ep p j) (axis p) = 0) ∧
    inner ℝ (axis p) (axis p) = 1 ∧
    ∀ x y : Fin p.b → ℝ,
      ‖∑ j, (x j • e p j + y j • ep p j)‖ ^ 2 = ∑ j, (x j ^ 2 + y j ^ 2) := by sorry

end ExactKMeans.ProductReduction
