-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint
-- name    : CerednikDrinfeld.Omega.theta_mul_theta_basePoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/9fe2ddd1-369e-55c2-aa79-91f397be0610
-- title:
--   Base-point cocycle for the theta product
-- statement:
--   Let $K_0$ be a field and $K$ a field extension of $K_0$ carrying a Hausdorff topological ring structure, let $G$ be a group and $\rho\colon G\to\mathrm{PGL}_2(K_0)$ a group homomorphism. For $x,y,c,d\in K$ write $\theta_\rho(a,b;c;d)$ for the unconditional product $\prod'_{\gamma\in G}$ of the factors $\gamma\mapsto [d,c;\,\mathrm{pmoebius}\,(\rho\gamma)(a),\ \mathrm{pmoebius}\,(\rho\gamma)(b)]$, the cross-ratio in $K$ of $d$, $c$ and the images of $a$ and $b$ under the Möbius action of $\rho\gamma$ on $K$ (more precisely: the action of $\rho\gamma$ on $\mathbb{P}^1(K)=$ `OnePoint K`, followed by the map sending $\infty$ to $0$ and fixing affine points). Given $a,b,z_0,z,w\in K$, assume that for every $\gamma\in G$ the points $\mathrm{pmoebius}\,(\rho\gamma)(a)$ and $\mathrm{pmoebius}\,(\rho\gamma)(b)$ are both different from $z$, and assume the two families of cross-ratio factors attached to the data $(a,b;z_0;z)$ and to $(a,b;z;w)$ are multipliable. Then $$\theta_\rho(a,b;z_0;z)\cdot\theta_\rho(a,b;z;w)=\theta_\rho(a,b;z_0;w).$$
--
--   This is the base-point cocycle relation for the Manin–Drinfeld theta products built from $G$-orbits of cross-ratios on the Drinfeld upper half plane: changing the normalisation point multiplies the theta function by a constant, so that the associated automorphy multipliers and periods do not depend on the base point. It is used in the analysis of products of theta functions over the Schottky group, in particular in the statements computing $\prod_\gamma\theta$ along cycles and the valuations of such products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_mul_theta_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z w : K}
    (hza : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hzb : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z)
    (h₀ : ThetaMultipliable ρ a b z₀ z) (h₁ : ThetaMultipliable ρ a b z w) :
    theta ρ a b z₀ z * theta ρ a b z w = theta ρ a b z₀ w := by sorry
