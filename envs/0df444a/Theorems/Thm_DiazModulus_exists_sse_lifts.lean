-- Prove2me | Theorems.Thm_DiazModulus_exists_sse_lifts
-- name    : DiazModulus.exists_sse_lifts
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:12.385998+00:00
-- url     : https://prove2.me/theorems/f65b3969-fbab-4f51-8ecd-e780dc59a4bf
-- title:
--   Restriction of scalars: if every $x_i y_j$ lies in ℒ̃, there are a ℚ-free algebraic $\omega_1, \dots, \omega_m$ and lifts $\eta_{a,j}$ in Q̄² × ℒ²ᵐ with $\Upsilon(\eta_{a,j}) = \omega_a y_j x$
-- statement:
--   Here $\overline{\mathbb{Q}}$ is the field of algebraic numbers, $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic), and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Let $\Upsilon : \mathbb{C}^2 \times \mathbb{C}^{m \times 2} \to \mathbb{C}^2$ be the linear map $\Upsilon(u, v)_i = u_i + \sum_{k=1}^m \omega_k v_{k,i}$ (Roy's map, DALAG §11.6.2). Let $x \in \mathbb{C}^2$ and $y \in \mathbb{C}^3$ with $x_i y_j \in \widetilde{\mathcal{L}}$ for all $i, j$. Then there are $m \geq 1$, $\omega_1, \dots, \omega_m \in \overline{\mathbb{Q}}$ linearly independent over $\mathbb{Q}$, and $\eta_{a,j} = (\eta'_{a,j}, \eta''_{a,j}) \in \overline{\mathbb{Q}}^2 \times \mathcal{L}^{m \times 2}$ ($a \leq m$, $j \leq 3$) with $\Upsilon(\eta_{a,j}) = \omega_a y_j x$.
--
--   **Proof.** Write each $x_i y_j$ as a finite sum $\sum_l f_l g_l$ with $f_l \in \overline{\mathbb{Q}}$ and $g_l \in \{1\} \cup \mathcal{L}$. Let $K = \mathbb{Q}(\text{all } f_l)$, a number field, and $\omega$ a $\mathbb{Q}$-basis of $K$. For $c \in K$ and $g \in \{1\} \cup \mathcal{L}$, $cg$ has the shape $u + \sum_k \omega_k v_k$ with $u \in \overline{\mathbb{Q}}$, $v_k \in \mathcal{L}$: take $u = c$ if $g = 1$, and otherwise $c = \sum_k r_k\omega_k$ with $r_k \in \mathbb{Q}$ and $v_k = r_k g \in \mathcal{L}$ (`Diaz.exp_ratMul_isAlgebraic`). As $\mathcal{L}$ contains $0$ and is closed under addition, the shape survives finite sums; applied to $\omega_a x_i y_j$ it gives $\eta_{a,j}$.
--
--   **Novelty.** Classical; routine formalisation. The restriction of scalars of DALAG §11.6.2 (after Roy 1992).
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2 (the map Υ and the basis ω of a number field), after D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47. Uses Diaz.exp_ratMul_isAlgebraic. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem exists_sse_lifts (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hxy : ∀ i j, x i * y j ∈ LogAlgTilde) :
    ∃ (m : ℕ) (ω : Fin m → ℂ) (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)),
      0 < m ∧ LinearIndependent ℚ ω ∧ (∀ a, ω a ∈ Qbar) ∧
      (∀ p, (∀ i, (η p).1 i ∈ Qbar) ∧ ∀ q, (η p).2 q ∈ LogAlg) ∧
      ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x := by
  sorry

end DiazModulus
