-- Prove2me | Theorems.Thm_DiazModulus_sse_relRank_generic
-- name    : DiazModulus.sse_relRank_generic
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:03+00:00
-- url     : https://prove2.me/theorems/680eec15-bfe6-4464-8aca-966afa092877
-- title:
--   If T = Υ(V′ × L₁) meets ℂx only in 0, the relation lattice of the SSE points modulo (V′, φ) has rank at most 2m − dim L₁
-- statement:
--   Let $\Upsilon : \mathbb{C}^2 \times \mathbb{C}^{m \times 2} \to \mathbb{C}^2$ be the linear map $\Upsilon(u, v)_i = u_i + \sum_{k=1}^m \omega_k v_{k,i}$ (Roy's map, DALAG §11.6.2). Let $\omega_1, \dots, \omega_m \in \overline{\mathbb{Q}}$ be linearly independent over $\mathbb{Q}$, let $x \in \mathbb{C}^2$ and $y \in \mathbb{C}^3$ each be linearly independent over $\overline{\mathbb{Q}}$, and let $\eta_{a,j} = (\eta'_{a,j}, \eta''_{a,j}) \in \mathbb{C}^2 \times \mathbb{C}^{m \times 2}$ ($a \leq m$, $j \leq 3$) with $\Upsilon(\eta_{a,j}) = \omega_a y_j x$. Let $V' \subseteq \mathbb{C}^2$ be a subspace, $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{m \times 2}$ with common complex kernel $L_1$, and $T = \Upsilon(V' \times L_1)$. Let $\rho$ be the dimension of the $\mathbb{Q}$-span of the set of $s \in \mathbb{Z}^{m \times 3}$ with $\sum_p s_p \eta'_p \in V'$ and $\prod_i (\prod_p e^{s_p \eta''_{p,i}})^{\varphi_{k,i}} = 1$ for every $k$. Suppose $T \cap \mathbb{C}x = \{0\}$. Then $\rho \leq 2m - \dim L_1$.
--
--   **Proof.** The multiplicative condition reads $e^{\Psi(s)_k} = 1$ for the $\mathbb{C}$-linear map $\Psi(z)_k = \sum_i \varphi_{k,i} \sum_p z_p \eta''_{p,i}$, so the relation set is a subgroup $A \subseteq \mathbb{Z}^{m \times 3}$ with $\Psi(A) \subseteq 2\pi i\,\mathbb{Z}^q$. $\Psi$ is injective on $A$: if $\Psi(s) = 0$ then $\zeta = \sum_p s_p \eta_p \in V' \times L_1$, and $\Upsilon(\zeta) = (\sum_{a,j} s_{a,j}\omega_a y_j)\,x$ lies in $T \cap \mathbb{C}x = \{0\}$; as $x \neq 0$ the coefficient vanishes, and $s = 0$ by `DiazModulus.sse_independence_facts`. Then `DiazModulus.rank_le_of_injOn_lattice` bounds $\rho$ by $\dim\mathrm{range}\,\Psi \leq \dim\mathrm{range}\,\Phi = 2m - \dim L_1$, where $\Phi(v)_k = \sum_i \varphi_{k,i} v_i$ has kernel $L_1$.
--
--   **Novelty.** Not found in the sources read in this form; routine. One case of the analysis of the obstruction in Roy's argument (DALAG §11.6.2); it does not use that the obstruction is defined over $\overline{\mathbb{Q}}$.
-- source:
--   The setting of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, after D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47. Not found in the sources read in this form; routine. Uses DiazModulus.sse_independence_facts and DiazModulus.rank_le_of_injOn_lattice. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem sse_relRank_generic (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (η : Fin m × Fin 3 → (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ))
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) (η p) = (ω p.1 * y p.2) • x)
    (V' : Submodule ℂ (Fin 2 → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin 2 → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin 2 → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0)
    (hT : ((V'.prod L₁).map (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) ⊓ (ℂ ∙ x) = ⊥) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin 3 → ℤ => fun j => (s j : ℚ)) ''
          {s : Fin m × Fin 3 → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}))
      ≤ 2 * m - Module.finrank ℂ ↥L₁ := by
  sorry

end DiazModulus
