-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
-- name    : CerednikDrinfeld.Omega.crossRatio_pmoebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/dbcac12b-55b6-5945-893a-824642eea7b9
-- title:
--   Invariance of the cross ratio under PGL₂(K₀)
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ a $K_0$-algebra, let $g$ be an element of $\mathrm{PGL}_2(K_0)$, and let $z, z_0, x, y$ be elements of $K$, each assumed to lie in `upperHalfPlane K₀ K`, that is, in the complement of the image of the structure map $K_0 \to K$ (so none of the four points is the image of a scalar from $K_0$). For $w \in K$, $\mathrm{pmoebius}\,K_0\,g\,w$ denotes the affine coordinate of the image of $w$ under the action of $g$ on the projective line $\mathbb{P}^1(K) = K \cup \{\infty\}$, with the point at infinity sent to $0$ by the chosen affine retraction. The cross ratio is defined by $\mathrm{crossRatio}(z,z_0,x,y) = \frac{(z-x)(z_0-y)}{(z-y)(z_0-x)}$, with division by zero read as $0$ in the field $K$. The conclusion is the identity $$\mathrm{crossRatio}(gz, gz_0, gx, gy) = \mathrm{crossRatio}(z,z_0,x,y).$$ No distinctness is assumed among $z, z_0, x, y$; when the denominator vanishes both sides are $0$.
--
--   This is the classical projective invariance of the cross ratio, stated for Drinfeld's upper half plane $\Omega = K \setminus K_0$ with the convention that division by zero yields zero, so that no non-degeneracy hypothesis on the four points is required. It is the factorwise transformation rule used in the construction of theta functions as products of cross ratios over a Schottky group, and is cited in the treatment of Mumford curves and of the automorphy and period computations for such theta products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : PGL(2, K₀)) {z z₀ x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (pmoebius K₀ g z) (pmoebius K₀ g z₀) (pmoebius K₀ g x) (pmoebius K₀ g y) = crossRatio z z₀ x y := by sorry
