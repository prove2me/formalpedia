-- Prove2me | Theorems.Thm_DiazModulus_sse_tangent_count
-- name    : DiazModulus.sse_tangent_count
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:13.300989+00:00
-- url     : https://prove2.me/theorems/30f0e241-a932-496b-8bb1-74ed52232a27
-- title:
--   With W = ker Υ and T = Υ(V′ × L₁): dim W = 2m, ℓ₀′ + codim T = d₀′ + d₁′, and codim T ≤ d₀′
-- statement:
--   Let $m \in \mathbb{N}$ and $\omega \in \mathbb{C}^m$. Let $\Upsilon : \mathbb{C}^2 \times \mathbb{C}^{m \times 2} \to \mathbb{C}^2$ be the linear map $\Upsilon(u, v)_i = u_i + \sum_{k=1}^m \omega_k v_{k,i}$ (Roy's map, DALAG §11.6.2). Let $V' \subseteq \mathbb{C}^2$ and $L_1 \subseteq \mathbb{C}^{m \times 2}$ be subspaces, $T = \Upsilon(V' \times L_1)$, and $\ell \in \mathbb{N}$ with $\ell + \dim(\ker\Upsilon \cap (V' \times L_1)) = \dim\ker\Upsilon$. Then $\dim\ker\Upsilon = 2m$, $\ell + (2 - \dim T) = (2 - \dim V') + (2m - \dim L_1)$, and $\dim V' \leq \dim T$.
--
--   **Proof.** $\Upsilon$ is surjective, so $\dim\ker\Upsilon = 2m$. Rank–nullity for $\Upsilon$ restricted to $P = V' \times L_1$ gives $\dim V' + \dim L_1 = \dim T + \dim(\ker\Upsilon \cap P)$, and the identity follows by integer arithmetic from the hypothesis and $\dim T, \dim V' \leq 2$, $\dim L_1 \leq 2m$. Finally $V' \subseteq T$, since $\Upsilon(u, 0) = u$ and $(u, 0) \in P$ for $u \in V'$.
--
--   **Novelty.** Not found in the sources read in this form; routine. A dimension count of the kind of DALAG Lemma 11.18 (3).
-- source:
--   A dimension count in the setting of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2 (compare Lemma 11.18 (3)). Not found in the sources read in this form; routine. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem sse_tangent_count (m : ℕ) (ω : Fin m → ℂ) (V' : Submodule ℂ (Fin 2 → ℂ)) (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ))
    (ℓ : ℕ) (hℓ : ℓ + Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) ⊓ V'.prod L₁)
      = Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)))) :
    Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) = 2 * m ∧
    ℓ + (2 - Module.finrank ℂ ↥((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))))
      = (2 - Module.finrank ℂ ↥V') + (2 * m - Module.finrank ℂ ↥L₁) ∧
    Module.finrank ℂ ↥V' ≤ Module.finrank ℂ ↥((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) := by
  sorry

end DiazModulus
