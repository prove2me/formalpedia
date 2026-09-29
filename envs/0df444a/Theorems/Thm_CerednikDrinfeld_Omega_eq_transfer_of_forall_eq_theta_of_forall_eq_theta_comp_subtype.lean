-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
-- name    : CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/95ec20da-e0fe-593c-8005-13ca5d0f01e0
-- title:
--   Theta multiplier of G equals the transfer from Γ'
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for it. Let $\varpi$ be a pseudo-uniformizer for the pair $(K_0,K)$, i.e. an element of $K_0$ whose valuation $\mathfrak p$ in $K$ satisfies $0<\mathfrak p<1$ and is such that every nonzero $a\in K_0$ has $\mathfrak p^{N}\le v(a)\le \mathfrak p^{-N}$ for some $N$; assume $\varpi$ is exhausting, meaning that every point of the Drinfeld upper half plane $\Omega=K\setminus\mathrm{im}(K_0\to K)$ lies in one of the affinoids $\mathrm{affinoid}\,\varpi\,n$, and that the ring $\mathrm{holRing}\,\varpi$ of functions on $\Omega$ that are holomorphic (uniform limits of uniformly bounded pole-free rational functions) on each of these affinoids is a domain. Let $G$ be a group and $\rho: G\to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for every $\varepsilon\in\Gamma_0$, $\varepsilon\ne 0$, there are only finitely many $\gamma\in G$ such that $\rho\gamma$ lifts to some $g\in \mathrm{GL}_2(K_0)$ with all entries of valuation $\le 1$ and $v(\det g)\ge\varepsilon$. Let $\Gamma'\le G$ be of finite index, and let $a',b',z_0\in\Omega$ be such that no $\rho\gamma$ ($\gamma\in G$) moves $a'$ or $b'$ to $z_0$ under the projective Möbius action. Suppose $c':\Gamma'\to K^\times$ is a homomorphism with $c'(\beta)=\theta_{\rho|_{\Gamma'}}(a',b';z_0)\bigl(\rho(\beta)z_0\bigr)$ for all $\beta\in\Gamma'$, where $\theta$ denotes the infinite product over the group of the cross-ratios $\mathrm{crossRatio}\,z\,z_0\,(\rho\gamma\,a')\,(\rho\gamma\,b')$, and $c:G\to K^\times$ is a homomorphism with $c(\beta)=\theta_{\rho}(a',b';z_0)\bigl(\rho(\beta)z_0\bigr)$ for all $\beta\in G$. Then $c$ equals the transfer (Verlagerung) of $c'$ along $\Gamma'\le G$.
--
--   This identifies the automorphy character of the Manin–Drinfeld theta function attached to the whole group $G$ with the transfer of the automorphy character of the theta function of a finite-index subgroup $\Gamma'$, for one and the same divisor $(a')-(b')$. It is used in the computation of period pairings and of uniformization data for $\mathrm{Pic}^0$ of Mumford quotients, where the projection formula relating periods for $G$ and for $\Gamma'$ is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Γ'.FiniteIndex]
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀)
    (c' : ↥Γ' →* Kˣ) (hc' : ∀ β : ↥Γ', ((c' β : Kˣ) : K) = theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ β) z₀))
    (c : G →* Kˣ) (hc : ∀ β : G, ((c β : Kˣ) : K) = theta ρ a' b' z₀ (pmoebius K₀ (ρ β) z₀)) :
    c = MonoidHom.transfer c' := by sorry
