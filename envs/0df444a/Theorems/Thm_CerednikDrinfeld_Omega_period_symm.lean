-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_period_symm
-- name    : CerednikDrinfeld.Omega.period_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/d3003615-76e2-578d-9515-05607a01aae7
-- title:
--   Symmetry of the Manin–Drinfeld period pairing
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is itself a field, equipped with a Hausdorff topological ring structure and with decidable equality, and let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$. Write $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ for `upperHalfPlane K₀ K`, the complement of the image of the structure map, and for $g \in \mathrm{PGL}_2(K_0)$ let $\mathrm{pmoebius}$ denote the induced fractional-linear action on $K$ obtained from the action on $\mathbb{P}^1(K) =$ `OnePoint K` followed by the retraction sending $\infty$ to $0$. Assume $a, z_0, w \in \Omega$; that no $\rho(\gamma)$ carries $a$ to $z_0$ and none carries $z_0$ to $a$; that no $\rho(\gamma)$ carries $a$ to $w$ and none carries $z_0$ to $w$; and that for all $x, y, u, z \in \Omega$ the family $\gamma \mapsto \mathrm{crossRatio}\, z\, u\, (\rho(\gamma)x)\, (\rho(\gamma)y)$ is multipliable over $G$. Then for all $\alpha, \beta \in G$ the period $\mathrm{period}\,\rho\,a\,z_0\,\alpha\,\beta$, namely the unconditional product $\prod_{\gamma \in G} \mathrm{crossRatio}\,(\rho(\beta)z_0)\, z_0\, (\rho(\gamma)a)\, (\rho(\gamma)\rho(\alpha)a)$, is unchanged when $\alpha$ and $\beta$ are interchanged.
--
--   This is the symmetry $Q(\alpha,\beta) = Q(\beta,\alpha)$ of the Manin–Drinfeld period pairing attached to a group acting on the Drinfeld upper half plane by fractional-linear transformations. It feeds the construction of the period pairing as a symmetric bi-multiplicative form, used in [`CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period`](thm.html#CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period) and in the statement relating periods to powers of the stabiliser width.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_period_symm.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.period_symm
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a)
    (hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ w) (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u z)
    (α β : G) :
    period ρ a z₀ α β = period ρ a z₀ β α := by sorry
