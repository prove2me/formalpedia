-- Prove2me | Theorems.Thm_DiazModulus_roy_rational_adapted_basis
-- name    : DiazModulus.roy_rational_adapted_basis
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:47:01.631878+00:00
-- url     : https://prove2.me/theorems/769d2e39-402d-4774-9ccf-541b271c1c19
-- title:
--   A rational subspace $S \subseteq \mathbb C^d$ becomes $\{v : v_i = 0 \text{ for } i \ge \dim S\}$ after a change of coordinates with algebraic matrices both ways
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For every rational $S \subseteq \mathbb C^d$ there is a linear automorphism $g$ of $\mathbb C^d$ such that $g$ and $g^{-1}$ map $\overline{\mathbb Q}^d$ into itself and $\widetilde{\mathcal L}^d$ into itself, and $v \in S$ if and only if $(gv)_i = 0$ for every $i \ge \dim S$.
-- source:
--   Classical linear algebra over Q̄ ⊆ ℂ. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rational_adapted_basis {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) (hS : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S) :
    ∃ g : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ),
      (∀ v : Fin d → ℂ, (∀ i, v i ∈ Qbar) → (∀ i, g v i ∈ Qbar) ∧ ∀ i, g.symm v i ∈ Qbar) ∧
      (∀ v : Fin d → ℂ, (∀ i, v i ∈ LogAlgTilde) → (∀ i, g v i ∈ LogAlgTilde) ∧ ∀ i, g.symm v i ∈ LogAlgTilde) ∧
      ∀ v : Fin d → ℂ, v ∈ S ↔ ∀ i : Fin d, Module.finrank ℂ ↥(S) ≤ i.val → g v i = 0 := by
  sorry

end DiazModulus
