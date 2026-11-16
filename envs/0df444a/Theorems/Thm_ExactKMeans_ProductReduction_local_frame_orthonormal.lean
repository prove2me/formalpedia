-- Prove2me | Theorems.Thm_ExactKMeans_ProductReduction_local_frame_orthonormal
-- name    : ExactKMeans.ProductReduction.local_frame_orthonormal
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T18:46:07.316246+00:00
-- url     : https://prove2.me/theorems/8be8abf4-377e-48ac-998a-216788d9481e
-- title:
--   Orthonormality of the local selector frame (equation (9))
-- statement:
--   Let $a,b\ge1$ with $ab\ge2$ and odd $t\ge3$ be the Section 5 parameters. Work in $\mathbb R^{2b+1}$ with orthonormal coordinate vectors $e_j,e_j^\perp$ $(j=1,\dots,b)$ and the axis vector $\hat e$. Put $\bar e=\frac1{\sqrt b}\sum_j e_j$ and $\bar e^\perp=\frac1{\sqrt b}\sum_j e_j^\perp$, $\theta_i=\arcsin(i/a^2)$ and $\beta=\arcsin\big(1/(4a^2\sqrt b)\big)$. The averaged vectors of selector $i$ are
--
--   $$
--   \bar e_i=\cos\theta_i\,\bar e-\sin\theta_i\,\bar e^\perp,\qquad
--   \bar e_i^\perp=\sin\beta\big(\sin\theta_i\,\bar e+\cos\theta_i\,\bar e^\perp\big)+\cos\beta\,\hat e,
--   $$
--
--   and its local basis vectors (equation (9)) are
--
--   $$
--   e_{i,j}=\cos\theta_i\Big(e_j-\tfrac{\bar e}{\sqrt b}\Big)+\sin\theta_i\Big(e_j^\perp-\tfrac{\bar e^\perp}{\sqrt b}\Big)+\tfrac{\bar e_i}{\sqrt b},
--   $$
--
--   $$
--   e_{i,j}^\perp=-\sin\theta_i\Big(e_j-\tfrac{\bar e}{\sqrt b}\Big)+\cos\theta_i\Big(e_j^\perp-\tfrac{\bar e^\perp}{\sqrt b}\Big)+\tfrac{\bar e_i^\perp}{\sqrt b}.
--   $$
--
--   For every selector $i$:
--
--   1. the vectors $e_{i,1},\dots,e_{i,b},e^\perp_{i,1},\dots,e^\perp_{i,b}$ form an orthonormal family, that is, $\langle e_{i,j},e_{i,k}\rangle=\langle e^\perp_{i,j},e^\perp_{i,k}\rangle=[j=k]$ and $\langle e_{i,j},e^\perp_{i,k}\rangle=0$ for all $j,k$;
--   2. every $e_{i,j}$ is orthogonal to the axis: $\langle e_{i,j},\hat e\rangle=0$;
--   3. the axis vector is a unit vector: $\langle\hat e,\hat e\rangle=1$.
--
--   The reference centers $\hat\mu^\pm_i(s)=O_i\pm\frac{r}{\sqrt b}\sum_j e_{i,j}(s_j)$ of equation (11) are built from rotations of this frame inside the planes $\operatorname{span}(e_{i,j},e^\perp_{i,j})$. Orthonormality turns norms of such combinations into sums of squares, and orthogonality to $\hat e$ shows that the zero-state reference centers project onto the axis exactly at $O_i$. This is the frame property behind Lemma 16 and the other distance computations of Section 5.
--
--   **Formalization Note** Selector indices are zero-based, with source index $i$ equal to `i.val + 1`; the axis is the last coordinate of $\mathbb R^{2b+1}$, and $[j=k]$ denotes the Kronecker delta.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 34–38 (PDF 35–39), equation (9) and the displayed formulas following it (local basis of selector i); frame property used in the proof of Lemma 16, printed p. 36 (PDF 37)

import Definitions.Def_ExactKMeans_ProductReduction_Placement

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace ExactKMeans.ProductReduction

theorem local_frame_orthonormal (p : Parameters) (i : Fin p.a) :
    (∀ j k : Fin p.b, inner ℝ (localE p i j) (localE p i k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (localEP p i j) (localEP p i k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (localE p i j) (localEP p i k) = 0) ∧
    (∀ j : Fin p.b, inner ℝ (localE p i j) (axis p) = 0) ∧
    inner ℝ (axis p) (axis p) = 1 := by sorry

end ExactKMeans.ProductReduction
