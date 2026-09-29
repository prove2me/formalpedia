-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
-- name    : CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/e82d8ebb-3df5-578f-9a45-28875c62d68d
-- title:
--   Base-point independence of the theta automorphy multiplier
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, carrying a Hausdorff topological ring structure, let $G$ be a group and $\rho\colon G\to \mathrm{PGL}(2,K_0)$ a group homomorphism. Write $\Omega = K\setminus \mathrm{image}(K_0\to K)$ for the set `upperHalfPlane K₀ K`, i.e. the complement of the range of the structure map, and for $g\in \mathrm{PGL}(2,K_0)$ let $g\cdot z$ denote `pmoebius K₀ g z`, the result of acting by $g$ on $z$ viewed in $\mathbb{P}^1(K)=$ `OnePoint K` and then returning to $K$ by sending $\infty$ to $0$. For $a,b,w,z\in K$ put $\Theta(a,b;w;z) = \prod'_{\gamma\in G} [z,w;\rho(\gamma)\cdot a,\rho(\gamma)\cdot b]$, the unconditional product of the cross-ratios `thetaFactor`. Assume $a,b,z_0,z_1\in\Omega$; that no point of the $\rho(G)$-orbit of $a$ or of $b$ equals $z_0$, and likewise none equals $z_1$; and that for all $w,z\in\Omega$ the family $\gamma\mapsto [z,w;\rho(\gamma)\cdot a,\rho(\gamma)\cdot b]$ is multipliable. Then for every $\beta\in G$, $\Theta(a,b;z_1;\rho(\beta)\cdot z_1) = \Theta(a,b;z_0;\rho(\beta)\cdot z_0)$.
--
--   This is the statement that the automorphy multiplier of the cross-ratio theta product attached to $\rho$ and the pair $(a,b)$ — and hence the Manin–Drinfeld period of $\beta$ — does not depend on the choice of base point in $\Omega$ off the orbits of $a$ and $b$. It is used in the construction of the period pairing on the Mumford quotient, in particular for the symmetry of the periods and for the computation of products of thetas along path cycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z₁ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (hz₁b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₁)
    (hΘ : ∀ w ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b w z) (β : G) :
    theta ρ a b z₁ (pmoebius K₀ (ρ β) z₁) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) := by sorry
