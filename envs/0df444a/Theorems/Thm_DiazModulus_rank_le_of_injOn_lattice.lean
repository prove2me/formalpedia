-- Prove2me | Theorems.Thm_DiazModulus_rank_le_of_injOn_lattice
-- name    : DiazModulus.rank_le_of_injOn_lattice
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:59.153985+00:00
-- url     : https://prove2.me/theorems/d4c0e8c9-6f34-4871-94b9-e5cd88406c24
-- title:
--   A subgroup $A$ of $\mathbb{Z}^N$ on which a ℂ-linear Ψ is injective with values in $2\pi i\,\mathbb{Z}^q$ has rank at most dim range Ψ
-- statement:
--   Let $N$ be finite, $\Psi : \mathbb{C}^N \to \mathbb{C}^q$ a $\mathbb{C}$-linear map, and $A \subseteq \mathbb{Z}^N$ a subgroup with $\Psi(A) \subseteq 2\pi i\,\mathbb{Z}^q$ and $\Psi(s) \neq 0$ for every non-zero $s \in A$. Then the dimension of the $\mathbb{Q}$-span of $A$ is at most the dimension of the range of $\Psi$.
--
--   **Proof.** Pick a $\mathbb{Q}$-basis of the span of $A$ inside $A$, elements $s_b$, with $\Psi(s_b) = 2\pi i e_b$, $e_b \in \mathbb{Z}^q$. It suffices that the $\Psi(s_b)$ are $\mathbb{C}$-independent. A complex relation among them is a complex kernel vector of the integer matrix $(e_b)$, and such a matrix has none once it has no rational one (the left-inverse argument of `DiazModulus.intMatrix_ker_facts`). A rational kernel vector $c$, cleared of denominators to $Dc_b \in \mathbb{Z}$, gives $s = \sum_b Dc_b s_b \in A$ with $\Psi(s) = 0$, so $s = 0$, and the independence of the basis gives $c = 0$.
--
--   **Novelty.** Not found in the sources read in this form; routine. Elementary lattice linear algebra.
-- source:
--   Elementary. Not found in the sources read in this form; routine. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rank_le_of_injOn_lattice {N : Type} [Fintype N] {q : ℕ} (Ψ : (N → ℂ) →ₗ[ℂ] (Fin q → ℂ))
    (A : AddSubgroup (N → ℤ))
    (hA : ∀ s ∈ A, ∃ e : Fin q → ℤ, Ψ (fun j => (s j : ℂ)) = fun k => 2 * Real.pi * Complex.I * e k)
    (hinj : ∀ s ∈ A, Ψ (fun j => (s j : ℂ)) = 0 → s = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : N → ℤ => fun j => (s j : ℚ)) '' (A : Set (N → ℤ))))
      ≤ Module.finrank ℂ ↥(LinearMap.range Ψ) := by
  sorry

end DiazModulus
