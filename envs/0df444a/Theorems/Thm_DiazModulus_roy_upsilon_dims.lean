-- Prove2me | Theorems.Thm_DiazModulus_roy_upsilon_dims
-- name    : DiazModulus.roy_upsilon_dims
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:47:40.318761+00:00
-- url     : https://prove2.me/theorems/bfc4c938-ce62-4c71-8237-caef32328659
-- title:
--   For Roy's map Υ: $\dim \Upsilon^{-1}(U) = \dim U + md$, $\ker\Upsilon$ is spanned by the vectors $(-\omega_k e_i, e_{k,i})$, and $\dim(\ker\Upsilon + X) = md + \dim\Upsilon(X)$
-- statement:
--   For $\omega \in \mathbb C^m$, $\Upsilon : \mathbb C^d \times \mathbb C^{m \times d} \to \mathbb C^d$ is Roy's map $\Upsilon(x, y)_i = x_i + \sum_{k=1}^m \omega_k y_{k,i}$ (DALAG §11.6.2), and $\Upsilon_1(y) = \Upsilon(0, y)$.
--
--   For every subspace $U \subseteq \mathbb C^d$ and every subspace $X \subseteq \mathbb C^d \times \mathbb C^{m \times d}$: $\dim \Upsilon^{-1}(U) = \dim U + md$; $\ker\Upsilon$ is spanned by the vectors $(-\omega_k e_i,\ e_{k,i})$ ($k \le m$, $i \le d$); and $\dim(\ker\Upsilon + X) = md + \dim \Upsilon(X)$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, Lemma 11.18 (1)–(2). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_upsilon_dims {d m : ℕ} (ω : Fin m → ℂ) (U : Submodule ℂ (Fin d → ℂ))
    (X : Submodule ℂ ((Fin d → ℂ) × (Fin m × Fin d → ℂ))) :
    Module.finrank ℂ ↥(U.comap (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ))) = Module.finrank ℂ ↥(U) + m * d ∧
    Submodule.span ℂ (Set.range (fun p : Fin m × Fin d =>
        ((fun i => if i = p.2 then -ω p.1 else 0), (fun q => if q = p then (1 : ℂ) else 0)))) =
      LinearMap.ker (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) ∧
    Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) ⊔ X) = m * d + Module.finrank ℂ ↥(X.map (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ))) := by
  sorry

end DiazModulus
