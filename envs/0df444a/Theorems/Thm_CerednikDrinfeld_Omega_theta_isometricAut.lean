-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_isometricAut
-- name    : CerednikDrinfeld.Omega.theta_isometricAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/ed2ec49b-3aa8-5475-8e19-cac699e78cb0
-- title:
--   Equivariance of the theta product under isometric automorphisms
-- statement:
--   Fix a field $K_0$ and a field extension $K$ of $K_0$ whose topology comes from a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, together with a group $G$ and a homomorphism $\rho \colon G \to \mathrm{PGL}(2, K_0)$. Let $s$ be an `IsometricAut K₀ K`, that is, a ring automorphism $s$ of $K$ such that $v(s(x)) = v(x)$ for all $x \in K$ and $s(\iota(a)) = \iota(a)$ for every $a \in K_0$, where $\iota \colon K_0 \to K$ is the structure map. Let $a, b, z_0, z$ be elements of $K$ lying in `upperHalfPlane K₀ K`, the complement of the image of $\iota$. Writing $\Theta_\rho(a,b;z_0;z)$ for `theta`, the unconditional product over $\gamma \in G$ of the cross-ratios $[z, z_0; \rho(\gamma)a, \rho(\gamma)b]$, where $\rho(\gamma)$ acts by the projective Möbius action `pmoebius` on $K$, the assertion is $$\Theta_\rho(s(a), s(b); s(z_0); s(z)) = s\bigl(\Theta_\rho(a,b;z_0;z)\bigr).$$ No convergence hypothesis is imposed: the identity holds for the unconditional product as defined, both sides taking the default value when it fails to converge.
--
--   This is the Galois-type equivariance of the Manin–Drinfeld theta product attached to a group of projective transformations defined over $K_0$: an isometric automorphism of $K$ fixing $K_0$ pointwise may be moved through $\Theta$. It is used in the study of the period pairing of the Mumford uniformisation, in particular in the construction of period data for the quotient curve and in the equivariance statements for the pinned uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_isometricAut.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_isometricAut
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (s : IsometricAut K₀ K) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    theta ρ (s.toRingEquiv a) (s.toRingEquiv b) (s.toRingEquiv z₀) (s.toRingEquiv z) =
      s.toRingEquiv (theta ρ a b z₀ z) := by sorry
