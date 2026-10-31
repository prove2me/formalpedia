-- Prove2me | Theorems.Thm_DiazModulus_exists_coordinate_section_mul
-- name    : DiazModulus.exists_coordinate_section_mul
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:49.660917+00:00
-- url     : https://prove2.me/theorems/551961c0-ca96-4eb9-a47d-8e80ffd49852
-- title:
--   A subgroup $\Phi \le \mathbb{Z}^{A_1}$ has a coordinate set $J$ with $\Phi \cap \mathbb{Z}^J = 0$ and triangular rows $\psi_i \in \Phi$, $i \notin J$; their common kernel has dimension $|J|$
-- statement:
--   Let $A_1$ be a finite type and $\Phi$ a subgroup of $\mathbb{Z}^{A_1}$. Then there are $J \subseteq A_1$ and $\psi_i \in \Phi$ ($i \in A_1$) such that the only element of $\Phi$ vanishing off $J$ is $0$, $\psi_i = 0$ for $i \in J$, $\psi_{i,i} \ne 0$ and $\psi_{i,i'} = 0$ for $i, i' \notin J$, $i' \ne i$, and every complex subspace $L \subseteq \mathbb{C}^{A_1}$ with $L = \{v : \sum_{i'} \psi_{i,i'} v_{i'} = 0 \text{ for every } i\}$ has $\dim L = |J|$.
--
--   **Proof.** Take $J$ of largest size with $\Phi \cap \mathbb{Z}^J = 0$. For $i \notin J$ maximality gives a non-zero $\psi_i \in \Phi$ supported on $J \cup \{i\}$, with $\psi_{i,i} \ne 0$. The system is triangular off $J$, so restriction to $J$ is a linear bijection from $L$ onto $\mathbb{C}^J$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical: a maximal coordinate set avoiding a lattice, and the triangular system it gives. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exists_coordinate_section_mul {A₁ : Type*} [Fintype A₁] (Φ : AddSubgroup (A₁ → ℤ)) :
    ∃ (J : Finset A₁) (ψ : A₁ → A₁ → ℤ), (∀ φ ∈ Φ, (∀ i ∉ J, φ i = 0) → φ = 0) ∧ (∀ i, ψ i ∈ Φ) ∧
      (∀ i ∈ J, ψ i = 0) ∧ (∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0) ∧
      ∀ L : Submodule ℂ (A₁ → ℂ), (∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0) → Module.finrank ℂ ↥L = J.card := by
  sorry

end DiazModulus
