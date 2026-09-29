-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
-- name    : CerednikDrinfeld.Omega.prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/19b3e30f-af55-5bd4-b53d-62b1617a845d
-- title:
--   Coset product of subgroup theta equals constant times theta
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for it. Let $\varpi$ be a pseudo-uniformizer, i.e. an element of $K_0$ with $0 < v(\varpi) < 1$ whose powers bracket the valuation of every nonzero element of $K_0$; assume $\varpi$ is exhausted, meaning every point of the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\ \varpi\ n$, and assume the ring $\mathrm{holRing}\ \varpi$ of functions on $\Omega$ that are uniform limits of uniformly bounded pole-free rational functions on each affinoid is a domain. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that, for each $\varepsilon \neq 0$ in $\Gamma_0$, only finitely many $\gamma$ admit a $\mathrm{GL}_2(K_0)$-lift of $\rho(\gamma)$ with all entries of valuation $\le 1$ and determinant of valuation $\ge \varepsilon$. Let $\Gamma' \le G$ have finite index, with $s : G/\Gamma' \to G$ a set-theoretic section of the quotient map. Let $a', b', z_0 \in \Omega$ with $z_0$ outside the $\rho(G)$-orbits (under the Möbius action $\mathrm{pmoebius}$) of $a'$ and of $b'$. Write $\Theta_H(z) = \prod'_{\gamma \in H} [\,z, z_0;\ \rho(\gamma)a',\ \rho(\gamma)b'\,]$ for the cross-ratio product over a group $H$ mapping to $\mathrm{PGL}_2(K_0)$, and put $C = \prod_{q \in G/\Gamma'} \Theta_{\Gamma'}(\rho(s q)^{-1} z_0)$, the product being over the finite quotient and $\Theta_{\Gamma'}$ formed with $\rho$ restricted to $\Gamma'$. The conclusion is the conjunction of two assertions: first, for every $z \in \Omega$, $\prod_{q} \Theta_{\Gamma'}(\rho(s q)^{-1} z) = C \cdot \Theta_G(z)$; second, in the fraction field $\mathrm{merField}\ \varpi$ of $\mathrm{holRing}\ \varpi$, the product over $q \in G/\Gamma'$ of the images of $\mathrm{thetaMer}\ \varpi\ (\rho|_{\Gamma'})\ a'\ b'\ z_0$ under the automorphisms $\mathrm{fracAct}$ induced by $\rho(s q)$ equals the image of $C$ under $\mathrm{algebraMap}\ K\ (\mathrm{merField}\ \varpi)$ times $\mathrm{thetaMer}\ \varpi\ \rho\ a'\ b'\ z_0$.
--
--   This is the norm relation for theta functions along a finite-index subgroup: the product over the cosets of $G/\Gamma'$ of the translates of the $\Gamma'$-theta function with divisor data $(a') - (b')$ is, up to the constant $C$, the $G$-theta function with the same data; the second clause records the same identity for the meromorphic avatars in the fraction field of the ring of holomorphic functions on the Drinfeld upper half plane, where $\mathrm{PGL}_2(K_0)$ acts. It is used in [`CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype`](thm.html#CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype), which identifies the automorphy character of the $G$-theta function as the transfer of that of the $\Gamma'$-theta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq.lean

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

theorem CerednikDrinfeld.Omega.prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀) :
    (∀ z ∈ upperHalfPlane K₀ K,
        ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z) =
          (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) * theta ρ a' b' z₀ z) ∧
      ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) =
        algebraMap K (merField ϖ) (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) *
          thetaMer ϖ ρ a' b' z₀ := by sorry
