-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period
-- name    : CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/0833b038-a1fa-53ef-80fe-b2c4cfe5d5f8
-- title:
--   Bimultiplicativity of the Manin–Drinfeld period pairing
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, carrying a topology making it a Hausdorff topological ring, and let $G$ be a group with a homomorphism $\rho\colon G\to \mathrm{PGL}_2(K_0)$. Write $\Omega = K\setminus \mathrm{image}(K_0\to K)$ for the set `upperHalfPlane K₀ K`, and for $g\in\mathrm{PGL}_2(K_0)$ and $z\in K$ let $g\cdot z$ denote `pmoebius`, the Möbius action of $g$ on $\mathbb{P}^1(K)=$ `OnePoint K` followed by the map sending $\infty$ to $0$ and fixing affine points. Let $a,z_0,w\in\Omega$ be such that $\rho(\gamma)\cdot a\neq z_0$, $\rho(\gamma)\cdot z_0\neq a$, $\rho(\gamma)\cdot a\neq w$ and $\rho(\gamma)\cdot z_0\neq w$ for every $\gamma\in G$, and assume that for all $x,y,u,z\in\Omega$ the family $\gamma\mapsto \mathrm{crossRatio}\,z\,u\,(\rho(\gamma)\cdot x)\,(\rho(\gamma)\cdot y)$ is multipliable over $G$ (the predicate `ThetaMultipliable`). Then there is a homomorphism $Q\colon G\to\mathrm{Hom}(G,K^\times)$ of groups, i.e. a map bimultiplicative in both arguments with values in the units of $K$, such that for all $\alpha,\beta\in G$ the image of $Q(\alpha)(\beta)$ in $K$ equals `period ρ a z₀ α β`, namely the infinite product $\prod_{\gamma\in G}\mathrm{crossRatio}\,(\rho(\beta)\cdot z_0)\,z_0\,(\rho(\gamma)\cdot a)\,(\rho(\gamma)\rho(\alpha)\cdot a)$.
--
--   This is the bimultiplicativity part of the Manin–Drinfeld theorem on periods of $p$-adic Schottky groups: the theta periods $\Theta(a,\alpha a;z_0;\beta z_0)$ form a pairing $G\times G\to K^\times$ multiplicative in each variable. It feeds the analysis of the period matrix of the Mumford curve attached to $\rho$, and is used in the study of the symmetrised pairing and its valuation on the stabiliser width.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a)
    (hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ w) (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u z) :
    ∃ Q : G →* G →* Kˣ, ∀ α β : G, ((Q α β : Kˣ) : K) = period ρ a z₀ α β := by sorry
