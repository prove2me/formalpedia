-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
-- name    : CerednikDrinfeld.Omega.theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b55c0e38-5039-5d75-b8ab-99f186d72431
-- title:
--   Theta as a product over cosets of a finite-index subgroup
-- statement:
--   Let $K_0$ be a field and $K$ a complete valued field (value group $\Gamma_0$) that is a $K_0$-algebra, and let $\varpi$ be a pseudo-uniformiser: an element of $K_0$ with $0 < v(\varpi) < 1$ whose powers scale every nonzero element of $K_0$ from both sides. Assume the affinoids $\{z : v(z) \le v(\varpi)^{-n},\ v(z-a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$ exhaust the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$, and that the ring `holRing` of functions on $\Omega$ that are, on each affinoid, uniform limits of a uniformly bounded sequence of pole-free rational functions is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism which is discrete in the sense that for each $\varepsilon \neq 0$ in $\Gamma_0$ only finitely many $\gamma$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho\gamma$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$. Let $\Gamma' \le G$ have finite index and $s : G/\Gamma' \to G$ be a set-theoretic section of the quotient map. Finally let $a, b, z_0 \in \Omega$ with $z_0$ outside the orbits of $a$ and of $b$ under the Möbius action of $\rho(G)$. Then two identities hold simultaneously: first, for every $z \in \Omega$, the unconditional product $\theta_G(a,b;z_0;z) = \prod'_{\gamma \in G} [z, z_0; \rho(\gamma)a, \rho(\gamma)b]$ equals $\prod_{q \in G/\Gamma'} \theta_{\Gamma'}\bigl(\rho(s q)^{-1}a, \rho(s q)^{-1}b; z_0; z\bigr)$, the factors being the corresponding products for the restriction $\rho \circ \Gamma'.\mathrm{subtype}$; secondly, the same identity for the meromorphic theta elements `thetaMer` in the fraction field of `holRing`, where `thetaMer` is $F/H$ for a chosen pair $(F,H)$ of holomorphic functions whose zero sets are the orbits of $a$ and of $b$ and whose quotient is the above product (and $0$ if no such pair exists).
--
--   This is the conorm, or restriction, identity for Schottky-type theta functions: the theta function attached to $G$ factors as the product of the theta functions attached to a finite-index subgroup $\Gamma'$ at the translated divisors, corresponding to pullback of the divisor $(a)-(b)$ along the finite covering of Mumford curves $X_{\Gamma'} \to X_G$. It is used by [`CerednikDrinfeld.Omega.comp_subtype_eq_prod_of_forall_eq_theta`](thm.html#CerednikDrinfeld.Omega.comp_subtype_eq_prod_of_forall_eq_theta) in the construction of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod.lean

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

theorem CerednikDrinfeld.Omega.theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    (∀ z ∈ upperHalfPlane K₀ K,
        theta ρ a b z₀ z =
          ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ z) ∧
      thetaMer ϖ ρ a b z₀ =
        ∏ q : G ⧸ Γ', thetaMer ϖ (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ := by sorry
