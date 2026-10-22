-- Prove2me | Theorems.Thm_DissipativePrep_Unique_monomial
-- name    : DissipativePrep.Unique.monomial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:07.150463+00:00
-- url     : https://prove2.me/theorems/d4a62d6f-e889-4694-bf6c-19105923f76b
-- title:
--   §IV, p. 4 — for χ ⊥ |0ⁿ⟩ some monomial P of the σ_-^{(k)} has ⟨0ⁿ|P|χ⟩ ≠ 0
-- statement:
--   Let $d_k = \sigma_-^{(k)}$, $k = 1,\dots,n$, be the qubit lowering operators. For every nonzero vector $\chi$ orthogonal to $|0^n\rangle$ there is a finite word $k_1,\dots,k_r$ (a monomial $P(\chi) = d_{k_1}\cdots d_{k_r}$ of the jump operators) such that
--   $$\langle 0^n|\,P(\chi)\,|\chi\rangle \neq 0.$$
--
--   This is the property that rules out a nonzero subspace invariant under all $d_k$ and orthogonal to $|0^n\rangle$, and hence (via Theorem 2) shows that $|0^n\rangle$ is the unique stationary state of $\mathcal L_{\{d_k\}}$.
--
--   **Formalization Note** "$|\chi\rangle$" is a state, so $\chi\neq 0$ is assumed (the zero vector is orthogonal to everything). The empty word is the identity.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV ("Furthermore, it is straightforward to show …")

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem monomial {n : ℕ} (χ : EuclideanSpace ℂ (Fin (2 ^ n))) (hχ : χ ≠ 0)
    (horth : inner ℂ (ket (0 : Fin (2 ^ n))) χ = 0) :
    ∃ w : List (Fin n), inner ℂ (ket (0 : Fin (2 ^ n))) (act (w.map lower).prod χ) ≠ 0 := by sorry

end DissipativePrep.Unique
