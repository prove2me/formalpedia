-- Prove2me | Theorems.Thm_DiazModulus_sse_relRank_rational
-- name    : DiazModulus.sse_relRank_rational
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:14.354982+00:00
-- url     : https://prove2.me/theorems/50fd1088-39a5-474b-8a6f-60025f716af3
-- title:
--   If T = Υ(V′ × L₁) lies in ℂx, then L₁ = 0 and the relation lattice of the SSE points modulo (V′, φ) is $\{0\}$; V′ need not be defined over Q̄
-- statement:
--   Let $\Upsilon : \mathbb{C}^2 \times \mathbb{C}^{m \times 2} \to \mathbb{C}^2$ be the linear map $\Upsilon(u, v)_i = u_i + \sum_{k=1}^m \omega_k v_{k,i}$ (Roy's map, DALAG §11.6.2). Let $\omega_1, \dots, \omega_m \in \overline{\mathbb{Q}}$ be linearly independent over $\mathbb{Q}$, let $x \in \mathbb{C}^2$ and $y \in \mathbb{C}^3$ each be linearly independent over $\overline{\mathbb{Q}}$, and let $\eta_{a,j} = (\eta'_{a,j}, \eta''_{a,j}) \in \mathbb{C}^2 \times \mathbb{C}^{m \times 2}$ ($a \leq m$, $j \leq 3$) with $\Upsilon(\eta_{a,j}) = \omega_a y_j x$. Suppose moreover $\eta'_{a,j} \in \overline{\mathbb{Q}}^2$ for all $a, j$. Let $V' \subseteq \mathbb{C}^2$ be a subspace, $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{m \times 2}$ with common complex kernel $L_1$, and $T = \Upsilon(V' \times L_1)$. Let $\rho$ be the dimension of the $\mathbb{Q}$-span of the set of $s \in \mathbb{Z}^{m \times 3}$ with $\sum_p s_p \eta'_p \in V'$ and $\prod_i (\prod_p e^{s_p \eta''_{p,i}})^{\varphi_{k,i}} = 1$ for every $k$. Suppose $T \subseteq \mathbb{C}x$. Then $L_1 = \{0\}$ and $\rho = 0$.
--
--   $V'$ is any subspace; it need not be defined over $\overline{\mathbb{Q}}$.
--
--   **Proof.** $L_1 = 0$: if $v \in \mathbb{Q}^{m \times 2}$ has $\langle \varphi_k, v \rangle = 0$ for all $k$, then $\Upsilon(0, v) \in T \subseteq \mathbb{C}x$ is algebraic, so it is $0$ by `DiazModulus.sse_independence_facts` (with $\beta = 1$), and $\sum_k \omega_k v_{k,i} = 0$ gives $v = 0$. So $\varphi$ has no rational kernel, hence no complex kernel (`DiazModulus.intMatrix_ker_facts`). Next, for $s$ in the relation set, $z = \sum_p s_p \eta''_p$ has $\langle \varphi_k, z \rangle \in 2\pi i\,\mathbb{Z}$, so $z = 2\pi i\,r$ with $r$ rational (`DiazModulus.intMatrix_ker_facts`). The vector $\sum_p s_p \eta'_p$ lies in $V' \subseteq T \subseteq \mathbb{C}x$ and is algebraic, so it is $0$. Then $(\sum_{a,j} s_{a,j}\omega_a y_j)\,x = \Upsilon(\sum_p s_p\eta_p) = 2\pi i\,(\sum_k \omega_k r_{k,i})_i$, an algebraic vector times $2\pi i \neq 0$, so the coefficient is $0$ and $s = 0$ (`DiazModulus.sse_independence_facts`). The relation set is $\{0\}$.
--
--   **Novelty.** Not found in the sources read in this form; routine. The other case of the analysis of the obstruction in Roy's argument (DALAG §11.6.2); it does not use that the obstruction is defined over $\overline{\mathbb{Q}}$.
-- source:
--   The setting of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, after D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47. Not found in the sources read in this form; routine. Uses DiazModulus.sse_independence_facts and DiazModulus.intMatrix_ker_facts. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem sse_relRank_rational (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x)
    (hηalg : ∀ p i, (η p).1 i ∈ Qbar)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) ≤ (ℂ ∙ x)) :
    L₁ = ⊥ ∧ Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) = 0 := by
  sorry

end DiazModulus
