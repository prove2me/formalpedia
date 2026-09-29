-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
-- name    : CerednikDrinfeld.Omega.apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/f3de30d0-3b1d-510b-9fb3-e7fe4f5e177b
-- title:
--   Möbius maps agreeing pointwise with a countable group lie in it
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ a $K_0$-algebra, and write $\Omega = \Omega_{K_0}(K)$ for the set `Omega.upperHalfPlane K₀ K`, namely the complement in $K$ of the image of the structure map $K_0 \to K$. For $h \in \mathrm{PGL}_2(K_0)$ and $z \in K$, `Omega.pmoebius K₀ h z` denotes the affine coordinate of the image of $z$ under the action of $h$ on $\mathbb{P}^1(K) =$ `OnePoint K`, the point at infinity being sent to $0$. Assume that $\Omega$ is not countable. Let $G$ be a group, $\rho : G \to \mathrm{PGL}_2(K_0)$ a group homomorphism, and $\Delta \leq G$ a subgroup whose image $\rho(\Delta)$ (as a subgroup of $\mathrm{PGL}_2(K_0)$) is countable. Let $g \in G$ be such that for every $z \in \Omega$ there exists $\delta \in \Delta$ with $\rho(g)\,z = \rho(\delta)\,z$, the equality being between the affine coordinates just described. Then $\rho(g)$ belongs to $\rho(\Delta)$.
--
--   This is the 'orbit-preserving implies member' step for the action of $\mathrm{PGL}_2(K_0)$ on Drinfeld's upper half plane $K \setminus K_0$: a transformation that, pointwise on $\Omega$, agrees with some element of a countable group of transformations already lies in that group. It is used in the Čerednik–Drinfeld part of the development, in the results deducing membership in $\rho(\Delta)$ from invariance of an invariant field together with a finite relative index condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    (hunc : ¬ (Omega.upperHalfPlane K₀ K).Countable)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    (Δ : Subgroup G) (hcount : Countable ↥(Δ.map ρ))
    (g : G)
    (hg : ∀ z ∈ Omega.upperHalfPlane K₀ K, ∃ δ ∈ Δ, Omega.pmoebius K₀ (ρ g) z = Omega.pmoebius K₀ (ρ δ) z) :
    ρ g ∈ Δ.map ρ := by sorry
