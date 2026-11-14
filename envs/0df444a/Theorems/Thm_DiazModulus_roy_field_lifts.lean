-- Prove2me | Theorems.Thm_DiazModulus_roy_field_lifts
-- name    : DiazModulus.roy_field_lifts
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:50:52.399386+00:00
-- url     : https://prove2.me/theorems/8d66436a-0a4a-4c52-9448-422bba302221
-- title:
--   Vectors in ℒ̃ᵈ lift through Roy's map: for a number field $k$ with $\mathbb Q$-basis $\omega$, $\Upsilon(\eta_{b,i}) = \omega_b z_i$ with $\eta_{b,i} \in k^d \times \mathcal L^{m \times d}$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $\omega \in \mathbb C^m$, $\Upsilon : \mathbb C^d \times \mathbb C^{m \times d} \to \mathbb C^d$ is Roy's map $\Upsilon(x, y)_i = x_i + \sum_{k=1}^m \omega_k y_{k,i}$ (DALAG §11.6.2), and $\Upsilon_1(y) = \Upsilon(0, y)$.
--
--   Let $z_1, \dots, z_\ell \in \widetilde{\mathcal L}^d$. Then there are $m \geq 1$ and $\mathbb Q$-linearly independent algebraic numbers $\omega_1, \dots, \omega_m$ whose $\mathbb Q$-span $k$ contains $1$ and is closed under multiplication (so $k$ is a number field), and vectors $\eta_{b,i} = (x, y)$ with $x \in k^d$ and $y \in \mathcal L^{m \times d}$, such that $\Upsilon(\eta_{b,i}) = \omega_b z_i$ for all $b \le m$, $i \le \ell$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, Lemma 11.18 (4), after D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, proof of Th. 4; lifts of a ℚ-basis replace the appeal to Baker's theorem. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_field_lifts {d ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hz : ∀ i j, z i j ∈ LogAlgTilde) :
    ∃ (m : ℕ) (ω : Fin m → ℂ) (η : Fin m × Fin ℓ → (Fin d → ℂ) × (Fin m × Fin d → ℂ)),
      0 < m ∧ LinearIndependent ℚ ω ∧ (∀ a, ω a ∈ Qbar) ∧
      (1 : ℂ) ∈ Submodule.span ℚ (Set.range ω) ∧
      (∀ a b, ω a * ω b ∈ Submodule.span ℚ (Set.range ω)) ∧
      (∀ p, (∀ i, (η p).1 i ∈ Submodule.span ℚ (Set.range ω)) ∧ ∀ q, (η p).2 q ∈ LogAlg) ∧
      ∀ p, (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) (η p) = ω p.1 • z p.2 := by
  sorry

end DiazModulus
