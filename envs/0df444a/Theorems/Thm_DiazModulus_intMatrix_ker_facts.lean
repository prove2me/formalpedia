-- Prove2me | Theorems.Thm_DiazModulus_intMatrix_ker_facts
-- name    : DiazModulus.intMatrix_ker_facts
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:22.012219+00:00
-- url     : https://prove2.me/theorems/5f163845-60a4-459a-9c9b-5127854e0b73
-- title:
--   An integer matrix with no rational kernel has no complex kernel, and if $\varphi z \in 2\pi i\,\mathbb{Z}^q$ then $z \in 2\pi i\,\mathbb{Q}^\iota$
-- statement:
--   Let $\iota$ be finite and $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^\iota$, and suppose the only $v \in \mathbb{Q}^\iota$ with $\langle \varphi_k, v \rangle = 0$ for all $k$ is $0$. Then the only such $v \in \mathbb{C}^\iota$ is $0$; and if $z \in \mathbb{C}^\iota$ has $\langle \varphi_k, z \rangle \in 2\pi i \mathbb{Z}$ for every $k$, then $z \in 2\pi i\,\mathbb{Q}^\iota$.
--
--   **Proof.** The map $v \mapsto (\langle \varphi_k, v \rangle)_k$ from $\mathbb{Q}^\iota$ to $\mathbb{Q}^q$ is injective, so it has a rational left inverse $B$, with $\sum_k B_{ik}\varphi_{k,j} = \delta_{ij}$; the identity persists over $\mathbb{C}$. So $w_i = \sum_k B_{ik} \langle \varphi_k, w \rangle$ for every complex $w$: this gives $w = 0$ when every $\langle \varphi_k, w \rangle$ is $0$, and $z_i = 2\pi i \sum_k B_{ik} e_k$ with $e_k \in \mathbb{Z}$ when $\langle \varphi_k, z \rangle = 2\pi i e_k$.
--
--   **Novelty.** Classical; routine formalisation. Linear algebra.
-- source:
--   Classical linear algebra. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem intMatrix_ker_facts {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ)
    (hφ : ∀ v : ι → ℚ, (∀ k, ∑ i, (φ k i : ℚ) * v i = 0) → v = 0) :
    (∀ v : ι → ℂ, (∀ k, ∑ i, (φ k i : ℂ) * v i = 0) → v = 0) ∧
    ∀ z : ι → ℂ, (∀ k, ∃ e : ℤ, ∑ i, (φ k i : ℂ) * z i = 2 * Real.pi * Complex.I * e) →
      ∃ v : ι → ℚ, ∀ i, z i = 2 * Real.pi * Complex.I * v i := by
  sorry

end DiazModulus
