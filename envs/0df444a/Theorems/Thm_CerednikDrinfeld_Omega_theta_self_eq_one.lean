-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_self_eq_one
-- name    : CerednikDrinfeld.Omega.theta_self_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/9871e6b3-7aae-5387-b658-943ba029cd20
-- title:
--   Cross-ratio theta product equals 1 at its base point
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure, with decidable equality and a topology on $K$, and let $G$ be a group with a homomorphism $\rho\colon G\to\mathrm{PGL}(2,K_0)$. Fix $a,b,z_0\in K$ and write $\gamma\cdot x$ for `pmoebius K₀ (ρ γ) x`, the image of $x$ under the Möbius action of $\rho(\gamma)$ on $\mathbb{P}^1(K)=$ `OnePoint K`, read back into $K$ by sending the point at infinity to $0$. Assume that for every $\gamma\in G$ one has $\gamma\cdot a\neq z_0$ and $\gamma\cdot b\neq z_0$, i.e. $z_0$ lies off the two orbits. Then the theta value $\Theta_\rho(a,b;z_0)(z_0)$ is $1$, where by definition `theta ρ a b z₀ z` is the unconditional infinite product $\prod'_{\gamma\in G}$ of the factors `crossRatio z z₀ (γ · a) (γ · b)`. No multipliability or convergence hypothesis is imposed; the conclusion holds because every individual factor is $1$.
--
--   This is the normalisation of the four-point cross-ratio theta product of a group acting on the projective line by fractional linear transformations, as used in the analytic uniformisation of Mumford curves. It is the base-point identity from which the multiplier of $\Theta$ is seen to be trivial on the identity, and it is invoked in the comparison of theta values at translated base points and in the statements about products of theta functions along cycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_self_eq_one.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_self_eq_one
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    theta ρ a b z₀ z₀ = 1 := by sorry
