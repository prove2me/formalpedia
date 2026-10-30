-- Prove2me | Theorems.Thm_DiazModulus_sse_setup
-- name    : DiazModulus.sse_setup
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:13.880018+00:00
-- url     : https://prove2.me/theorems/2ae6222d-959b-44c9-8ca2-e0294415f3dd
-- title:
--   For x ≠ 0, V = Υ⁻¹(ℂx) has dimension 2m + 1, and W = ker Υ is spanned by the vectors $(-\omega_k e_i, e_{k,i})$
-- statement:
--   Let $m \in \mathbb{N}$, $\omega \in \mathbb{C}^m$ and $x \in \mathbb{C}^2$ with $x \neq 0$. Let $\Upsilon : \mathbb{C}^2 \times \mathbb{C}^{m \times 2} \to \mathbb{C}^2$ be the linear map $\Upsilon(u, v)_i = u_i + \sum_{k=1}^m \omega_k v_{k,i}$ (Roy's map, DALAG §11.6.2). Then $\Upsilon^{-1}(\mathbb{C}x)$ has dimension $2m + 1$, and $\ker\Upsilon$ is spanned by the vectors $b_{k,i} = (-\omega_k e_i, e_{k,i})$ ($k \leq m$, $i = 1, 2$), where $e_i$ and $e_{k,i}$ are standard basis vectors.
--
--   **Proof.** $\Upsilon$ is surjective, as $\Upsilon(u, 0) = u$. Composed with the quotient map $\mathbb{C}^2 \to \mathbb{C}^2/\mathbb{C}x$, of dimension $1$ as $x \neq 0$, it is a surjection with kernel $\Upsilon^{-1}(\mathbb{C}x)$, and rank–nullity on a domain of dimension $2 + 2m$ gives $2m + 1$. Each $b_{k,i}$ lies in $\ker\Upsilon$, and every $z \in \ker\Upsilon$ equals $\sum_p z''_p b_p$, since $z'_i = -\sum_k \omega_k z''_{k,i}$ on the kernel.
--
--   **Novelty.** Classical; routine formalisation. Linear algebra of Roy's map, as in DALAG Lemma 11.18 (1)–(2).
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, Lemma 11.18 (1)–(2), after D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem sse_setup (m : ℕ) (ω : Fin m → ℂ) (x : Fin 2 → ℂ) (hx0 : x ≠ 0) :
    Module.finrank ℂ ↥((ℂ ∙ x).comap (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) = 2 * m + 1 ∧
    Submodule.span ℂ (Set.range (fun p : Fin m × Fin 2 => ((fun i => if i = p.2 then -ω p.1 else 0),
        (fun q => if q = p then (1 : ℂ) else 0))))
      = LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) := by
  sorry

end DiazModulus
