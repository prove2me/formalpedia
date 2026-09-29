-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem
-- name    : CerednikDrinfeld.FormalOmega.exists_finite_quotient_and_even_vdet_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/4375af37-2951-57cb-99f2-01aeabef0392
-- title:
--   A finite quotient of Γ with even determinant valuation
-- statement:
--   Let $\mathcal O$ be a commutative domain, $\pi \in \mathcal O$, and $K_0$ a field which is a fraction field of $\mathcal O$ via a given algebra structure. Let $v\!\det \colon \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively, as a homomorphism into `Multiplicative ℤ`) satisfy: for every $g$ and every $n \in \mathbb Z$, $v\!\det(g) = n$ if and only if $\det g = u\pi^n$ in $K_0$ for some unit $u \in \mathcal O^\times$ (images under the structure map). Let $G$ be a group, $\sigma \colon G \to \mathrm{GL}_2(K_0)$ a homomorphism, $\Gamma, \Gamma' \le G$ subgroups with $\Gamma' = \{x \in \Gamma : v\!\det(\sigma x) \text{ even}\}$ as sets, and $\rho \colon G \to \mathrm{PGL}_2(K_0)$ the homomorphism obtained pointwise as the projection `Matrix.ProjGenLinGroup.mk` of $\sigma$. Finally let $N \le \mathrm{PGL}_2(K_0)$ be a subgroup with $N \le \rho(\Gamma')$, such that $N \cap \rho(\Gamma)$, viewed inside $\rho(\Gamma)$, is normal there, and such that the relative index of $N$ in $\rho(\Gamma')$ is nonzero. Then there exist a finite group $G_2$ and a surjective homomorphism $\theta \colon \Gamma \to G_2$ such that for $\gamma \in \Gamma$ one has $\theta(\gamma) = 1$ exactly when $\rho(\gamma) \in N$, and such that $\rho(\gamma) \in N$ implies $v\!\det(\sigma\gamma)$ is even.
--
--   This is the group-theoretic step in the construction of the twisted Mumford tower in the Čerednik–Drinfeld setting: it produces the finite group through which a $p$-adic uniformising group acts, together with the parity statement on the valuation of $\det \sigma\gamma$ that makes the associated Frobenius twist well defined. It is used by [`CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.FormalOmega.exists_finite_quotient_and_even_vdet_of_mem

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0) :
    ∃ (G₂ : Type) (_ : Group G₂) (_ : Finite G₂) (θ : ↥Γ →* G₂),
      Function.Surjective θ ∧ (∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N) ∧
      (∀ γ : ↥Γ, ρ (γ : G) ∈ N → Even (Multiplicative.toAdd (vdet (σ (γ : G))))) := by sorry
