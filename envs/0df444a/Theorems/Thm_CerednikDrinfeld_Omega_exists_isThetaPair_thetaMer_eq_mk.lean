-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk
-- name    : CerednikDrinfeld.Omega.exists_isThetaPair_thetaMer_eq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/279e7c90-2663-56b1-bb7f-e6df37952eee
-- title:
--   thetaMer is represented by a theta pair
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for the associated topology. Let $\varpi$ be a pseudo-uniformiser of $K_0$ in $K$, that is an element with $0 < v(\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$, and assume `IsExhausted` $\varpi$: every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\,\varpi\,n$. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for every $\varepsilon \neq 0$ in $\Gamma_0$ only finitely many $\gamma \in G$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$. Let $a, b, z_0 \in \Omega$ with $z_0$ outside the orbits of $a$ and of $b$ under the Möbius action of $\rho(G)$. Then there exist $F, H$ in the ring $\mathrm{holRing}\,\varpi$ of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of pole-free rational functions, together with a proof $h$ that $(F,H)$ is a theta pair for $\rho, a, b, z_0$ — i.e. $H$ is a non-zero-divisor, $H(z) = 0$ exactly for $z$ in the $\rho(G)$-orbit of $b$, $F(z) = 0$ exactly for $z$ in the orbit of $a$, and $F(z)/H(z) = \mathrm{theta}\,\rho\,a\,b\,z_0\,z$ for every $z$ off the orbit of $b$ — such that the element $\mathrm{thetaMer}\,\varpi\,\rho\,a\,b\,z_0$ of the fraction field of $\mathrm{holRing}\,\varpi$ equals the fraction $F/H$.
--
--   This identifies the meromorphic theta function attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$, defined by a choice over the existence of a theta pair and set to $0$ otherwise, with an explicit quotient $F/H$; in particular the defining case distinction falls on the nontrivial branch. It is the basic access lemma for $\mathrm{thetaMer}$, used in establishing its transformation laws under the group action and its multiplicativity in the divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_isThetaPair_thetaMer_eq_mk
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H),
      thetaMer ϖ ρ a b z₀ = Localization.mk F ⟨H, h.1⟩ := by sorry
