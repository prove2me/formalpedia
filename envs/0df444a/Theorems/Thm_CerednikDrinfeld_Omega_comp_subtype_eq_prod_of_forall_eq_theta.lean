-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_comp_subtype_eq_prod_of_forall_eq_theta
-- name    : CerednikDrinfeld.Omega.comp_subtype_eq_prod_of_forall_eq_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/5f1a3362-5b40-5607-bd55-fb73c10080fe
-- title:
--   Restriction of the theta character to a finite-index subgroup
-- statement:
--   Fix a field $K_0$, a field extension $K$ of $K_0$ with decidable equality, a valuation $v$ on $K$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ complete. Let $\varpi$ be a pseudo-uniformizer for the pair $(K_0,K)$, that is an element of $K_0$ whose valuation lies strictly between $0$ and $1$ and such that every nonzero element of $K_0$ has valuation squeezed between a power of $v(\varpi)$ and the corresponding power of $v(\varpi)^{-1}$; assume $\varpi$ is exhausted, i.e. every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\ \varpi\ n$, and that the ring of functions holomorphic on all these affinoids is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ which is discrete in the sense that, for each $\varepsilon \neq 0$ in $\Gamma_0$, only finitely many $\gamma \in G$ admit a lift of $\rho(\gamma)$ to $\mathrm{GL}_2(K_0)$ with all entries of valuation $\le 1$ and determinant of valuation $\ge \varepsilon$. Let $\Gamma' \le G$ be a subgroup with finite coset space $G/\Gamma'$ and let $s : G/\Gamma' \to G$ be a section of the quotient map. Let $a,b,z_0 \in \Omega$ with $\mathrm{pmoebius}(\rho(\gamma))a \neq z_0$ and $\mathrm{pmoebius}(\rho(\gamma))b \neq z_0$ for all $\gamma \in G$, where $\mathrm{pmoebius}$ denotes the action of $\mathrm{PGL}_2(K_0)$ on $K \subseteq \mathbb{P}^1(K)$ followed by the affine chart. Let $c : G \to K^\times$ be a homomorphism with $c(\beta) = \theta_\rho(a,b;z_0)(\rho(\beta) z_0)$ for every $\beta \in G$, where $\theta_\rho(a,b;z_0)(z)$ is the (multipliable) infinite product over $\gamma \in G$ of the cross-ratios of $z, z_0, \rho(\gamma)a, \rho(\gamma)b$. Let $c'$ assign to each coset $q \in G/\Gamma'$ a homomorphism $c'_q : \Gamma' \to K^\times$ with $c'_q(\beta) = \theta_{\rho|_{\Gamma'}}(\rho(s q)^{-1}a, \rho(s q)^{-1}b; z_0)(\rho(\beta) z_0)$ for all $\beta \in \Gamma'$. The conclusion is the equality of homomorphisms $\Gamma' \to K^\times$: the restriction of $c$ along the inclusion $\Gamma' \hookrightarrow G$ equals $\prod_{q \in G/\Gamma'} c'_q$.
--
--   This is the multiplier (automorphy character) companion of the factorisation of a $G$-theta function into a product of $\Gamma'$-theta functions over the cosets of a finite-index subgroup: the character of the $G$-theta function, restricted to $\Gamma'$, is the product of the characters of the twisted $\Gamma'$-theta functions. It is used in the construction of equivariant uniformisations and of the resulting maps on degree-zero Picard groups for Mumford quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_comp_subtype_eq_prod_of_forall_eq_theta.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.comp_subtype_eq_prod_of_forall_eq_theta
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (c : G →* Kˣ) (hc : ∀ β : G, ((c β : Kˣ) : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (c' : G ⧸ Γ' → (↥Γ' →* Kˣ))
    (hc' : ∀ (q : G ⧸ Γ') (β : ↥Γ'), ((c' q β : Kˣ) : K) =
      theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ (pmoebius K₀ (ρ β) z₀)) :
    c.comp Γ'.subtype = ∏ q : G ⧸ Γ', c' q := by sorry
