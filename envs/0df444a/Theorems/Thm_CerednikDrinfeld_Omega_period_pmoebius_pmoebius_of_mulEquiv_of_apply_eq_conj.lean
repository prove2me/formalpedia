-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
-- name    : CerednikDrinfeld.Omega.period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3a661db3-bce6-57da-a8a1-7984870f9953
-- title:
--   Periods transport along a conjugating group isomorphism
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, equipped with a topology and with decidable equality, and let $G_1, G_2$ be groups. Given homomorphisms $\rho_1 : G_1 \to \mathrm{PGL}(2,K_0)$ and $\rho_2 : G_2 \to \mathrm{PGL}(2,K_0)$, a group isomorphism $e : G_1 \simeq G_2$, and an element $n \in \mathrm{PGL}(2,K_0)$ such that $\rho_2(e(g)) = n\,\rho_1(g)\,n^{-1}$ for every $g \in G_1$, let $a, z_0 \in K$ both lie in $\mathrm{upperHalfPlane}\,K_0\,K$, i.e. in the complement of the image of the structure map $K_0 \to K$. Here `pmoebius` $K_0\,g\,z$ denotes the affine part of the action of $g \in \mathrm{PGL}(2,K_0)$ on $z$ viewed in $\mathbb{P}^1(K) = \mathrm{OnePoint}\,K$ (the point at infinity being sent to $0$), and for $\rho : G \to \mathrm{PGL}(2,K_0)$ the period $\mathrm{period}\,\rho\,a\,z_0\,\alpha\,\beta$ is $\mathrm{theta}\,\rho\,a\,(\rho(\alpha)\cdot a)\,z_0\,(\rho(\beta)\cdot z_0)$, that is the unconditional product over all $\gamma \in G$ of `thetaFactor` at those arguments. The assertion is that for all $\alpha, \beta \in G_1$,
--   $$\mathrm{period}\,\rho_2\,(n\cdot a)\,(n\cdot z_0)\,(e\alpha)\,(e\beta) \;=\; \mathrm{period}\,\rho_1\,a\,z_0\,\alpha\,\beta.$$
--
--   This is the invariance of the multiplicative periods attached to a group of Möbius transformations acting on Drinfeld's upper half plane under simultaneous conjugation of the group by an element of $\mathrm{PGL}(2,K_0)$ and transport of the index group along an isomorphism; it covers in particular the comparison of the periods of a subgroup $H$ with those of a conjugate $n^{-1}Hn$ presented as a different group. It is used in the comparison of period pairings on $\mathrm{Pic}^0$ arising from Mumford quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ρ₁ : G₁ →* PGL(2, K₀)) (ρ₂ : G₂ →* PGL(2, K₀))
    (e : G₁ ≃* G₂) (n : PGL(2, K₀)) (he : ∀ g : G₁, ρ₂ (e g) = n * ρ₁ g * n⁻¹)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G₁) :
    period ρ₂ (pmoebius K₀ n a) (pmoebius K₀ n z₀) (e α) (e β) = period ρ₁ a z₀ α β := by sorry
