-- Prove2me | Theorems.Thm_DiazModulus_roy_intKer_image
-- name    : DiazModulus.roy_intKer_image
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:46:55.076634+00:00
-- url     : https://prove2.me/theorems/cddee12c-a966-45a0-970d-2982017836b3
-- title:
--   If $L_1$ is the kernel of an integer matrix and $\omega$ is $\mathbb Q$-free and algebraic, then $\dim L_1 \le m \dim \Upsilon_1(L_1)$ and $\Upsilon_1(L_1)$ is rational
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $\omega \in \mathbb C^m$, $\Upsilon : \mathbb C^d \times \mathbb C^{m \times d} \to \mathbb C^d$ is Roy's map $\Upsilon(x, y)_i = x_i + \sum_{k=1}^m \omega_k y_{k,i}$ (DALAG §11.6.2), and $\Upsilon_1(y) = \Upsilon(0, y)$.
--
--   Let $\omega_1, \dots, \omega_m$ be algebraic and linearly independent over $\mathbb Q$, and let $L_1 \subseteq \mathbb C^{m \times d}$ be the common kernel of finitely many integer linear forms. Then $\dim L_1 \le m \cdot \dim \Upsilon_1(L_1)$, and $\Upsilon_1(L_1)$ is a rational subspace of $\mathbb C^d$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, Lemma 11.18 (3) (the estimate d₁′ ≥ m d′), here without assuming that the obstruction subgroup is defined over Q̄. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_intKer_image {d m q : ℕ} (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω)
    (hωalg : ∀ a, ω a ∈ Qbar) (φ : Fin q → Fin m × Fin d → ℤ) (L₁ : Submodule ℂ (Fin m × Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℂ ↥(L₁) ≤ m * Module.finrank ℂ ↥(L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ))) ∧
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)) ∧ ∀ i, v i ∈ Qbar} = L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)) := by
  sorry

end DiazModulus
