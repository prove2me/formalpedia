-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta
-- name    : CerednikDrinfeld.Omega.exists_monoidHom_isAutomorphicWithMultiplier_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/28ab038c-344f-506c-aa4a-1ea8c44ca300
-- title:
--   Automorphy of the cross-ratio theta product with multiplier
-- statement:
--   Let $K_0$ be a field and $K$ a Hausdorff topological field that is a $K_0$-algebra, let $G$ be a group and $\rho\colon G\to \mathrm{PGL}(2,K_0)$ a homomorphism, acting on $K$ by $z\mapsto \mathrm{pmoebius}\,(\rho\gamma)\,z$, the affine trace of the action of $\rho\gamma$ on $\mathbb{P}^1(K)=\mathrm{OnePoint}\,K$ (the point at infinity being sent to $0$). Write $\Omega = \mathrm{upperHalfPlane}\,K_0\,K$ for the complement in $K$ of the image of $K_0$ under the structure map. Let $a,b,z_0\in\Omega$ be such that $\mathrm{pmoebius}\,(\rho\gamma)\,a\neq z_0$ and $\mathrm{pmoebius}\,(\rho\gamma)\,b\neq z_0$ for every $\gamma\in G$, and assume that for every $z\in\Omega$ the family of cross-ratios $\gamma\mapsto [z,z_0;\mathrm{pmoebius}\,(\rho\gamma)\,a,\mathrm{pmoebius}\,(\rho\gamma)\,b]$ is multipliable, so that the product $\Theta(z)=\mathrm{theta}\,\rho\,a\,b\,z_0\,z$ over $\gamma\in G$ is defined. Then there exists a monoid homomorphism $c\colon G\to K^\times$ such that $c(\beta)=\Theta(\mathrm{pmoebius}\,(\rho\beta)\,z_0)$ in $K$ for every $\beta\in G$, and such that $\Theta$ is automorphic on $\Omega$ with multiplier $c$, i.e. $\Theta(\mathrm{pmoebius}\,(\rho\gamma)\,z)=c(\gamma)\,\Theta(z)$ for all $\gamma\in G$ and all $z\in\Omega$.
--
--   This is the automorphy property of the Manin–Drinfeld theta product attached to a group of projective transformations acting on Drinfeld's upper half plane, with its multiplier realised as a genuine homomorphism to $K^\times$ whose value at $\beta$ is the theta value at $\beta z_0$. It is the input for the later construction of periods and of meromorphic theta quotients in this development, being used in the statements about finite-order elements, the period of the meromorphic theta function, and the multiplier homomorphism for the fractional action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_monoidHom_isAutomorphicWithMultiplier_theta
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hΘ : ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b z₀ z) :
    ∃ c : G →* Kˣ, (∀ β : G, (c β : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      IsAutomorphicWithMultiplier ρ (upperHalfPlane K₀ K) (theta ρ a b z₀) c := by sorry
