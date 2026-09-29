-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv
-- name    : CerednikDrinfeld.Omega.theta_pmoebius_basePoint_mul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1731750e-3324-542c-840b-31def8a09e11
-- title:
--   The theta multiplier is a unit: c(β)c(β⁻¹)=1
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure and a Hausdorff topological ring topology, and let $\rho\colon G\to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$. For $g\in\mathrm{PGL}_2(K_0)$ and $w\in K$, write $\mathrm{pmoebius}$ for the map sending $w$ to the affine value of $g\cdot w$ computed in $\mathbb{P}^1(K)=\mathrm{OnePoint}\,K$, with the point at infinity sent to $0$. Let $a,b,z_0\in K$ all lie in `upperHalfPlane K₀ K`, that is, outside the image of the structure map $K_0\to K$, and assume that $\mathrm{pmoebius}(\rho\gamma)(a)\neq z_0$ and $\mathrm{pmoebius}(\rho\gamma)(b)\neq z_0$ for every $\gamma\in G$. Here $\Theta$, written `theta`, denotes the unconditional product $\prod'_{\gamma\in G}$ of the cross-ratios $\mathrm{crossRatio}\, z\, z_0\, (\mathrm{pmoebius}(\rho\gamma)(a))\,(\mathrm{pmoebius}(\rho\gamma)(b))$. Let $\beta\in G$ and assume the two families of cross-ratio factors evaluated at $z=\mathrm{pmoebius}(\rho\beta)(z_0)$ and at $z=\mathrm{pmoebius}(\rho\beta^{-1})(z_0)$ are each multipliable. Then the two corresponding values of $\Theta$ multiply to $1$.
--
--   The quantity $c(\beta)=\Theta(a,b;z_0;\beta z_0)$ is the multiplier attached to $\beta$ by the cross-ratio theta product for a group acting on the Drinfeld upper half plane; the statement says it is invertible, with no completeness or valuation hypothesis on $K$. It is used in the construction of the multiplier homomorphism $\beta\mapsto c(\beta)$ (`exists_monoidHom_isAutomorphicWithMultiplier_theta`) and in the comparison of periods (`period_eq_period_of_mem_upperHalfPlane`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_basePoint_mul_inv
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (h : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h' : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀)) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀) = 1 := by sorry
