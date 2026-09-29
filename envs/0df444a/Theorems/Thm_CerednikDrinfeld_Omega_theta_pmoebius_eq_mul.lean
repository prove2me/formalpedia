-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul
-- name    : CerednikDrinfeld.Omega.theta_pmoebius_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/7c18674f-3ca6-50db-bf43-690df6e5ee9c
-- title:
--   Automorphy of the cross-ratio theta product under ρ(β)
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, equipped with a topology making it a Hausdorff topological ring, let $G$ be a group and $\rho \colon G \to \mathrm{PGL}_2(K_0)$ a group homomorphism. Write $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ for the set `upperHalfPlane K₀ K`, i.e. the complement of the image of the structure map, and for $g \in \mathrm{PGL}_2(K_0)$ let $g \cdot z$ denote `pmoebius K₀ g z`, the affine part of the action of $g$ on $z$ viewed in the one-point extension $\mathbb{P}^1(K)$ (the point at infinity being sent to $0$). For $a, b, z_0, z \in K$, `theta ρ a b z₀ z` is the unconditional product $\prod'_{\gamma \in G} [z, z_0; \rho(\gamma)\cdot a, \rho(\gamma)\cdot b]$ of cross-ratios, and `ThetaMultipliable ρ a b z₀ z` asserts that the family of these cross-ratios is multipliable. Assume $a, b, z_0, z \in \Omega$, that $\rho(\gamma)\cdot a \neq z_0$ and $\rho(\gamma)\cdot b \neq z_0$ for every $\gamma \in G$, and let $\beta \in G$. If the families defining `theta ρ a b z₀ z` and `theta ρ a b (ρ(β⁻¹)·z₀) z₀` are both multipliable, then $$\Theta(a,b;z_0;\rho(\beta)\cdot z) = \Theta(a,b;\rho(\beta^{-1})\cdot z_0; z_0)\cdot \Theta(a,b;z_0;z).$$
--
--   This is the automorphy (theta-transformation) property of the Manin–Drinfeld cross-ratio theta product attached to a group of Möbius transformations acting on the Drinfeld upper half plane: the multiplier $\Theta(a,b;\rho(\beta^{-1})\cdot z_0;z_0)$ depends on $a$, $b$, $z_0$ and $\beta$ but not on $z$. It is used to produce the multiplier homomorphism in [`CerednikDrinfeld.Omega.exists_monoidHom_isAutomorphicWithMultiplier_theta`](thm.html#CerednikDrinfeld.Omega.exists_monoidHom_isAutomorphicWithMultiplier_theta) and in [`CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint`](thm.html#CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_eq_mul
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ₀ : ThetaMultipliable ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z) =
      theta ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀ * theta ρ a b z₀ z := by sorry
