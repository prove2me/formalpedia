-- Prove2me | Theorems.Thm_DissipativePrep_Unique_dark_jumpOps
-- name    : DissipativePrep.Unique.dark_jumpOps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:05.982046+00:00
-- url     : https://prove2.me/theorems/57186c49-04b9-4349-b236-da1c7c392307
-- title:
--   §IV, p. 4 — c_kφ = 0 for all k iff φ is a multiple of U|0ⁿ⟩
-- statement:
--   Let $U$ be a unitary on $n$ qubits, $\sigma_-^{(k)} = \mathbb 1\otimes\dots\otimes|0\rangle_k\langle1|\otimes\dots\otimes\mathbb 1$, $c_k = U\sigma_-^{(k)}U^\dagger$ and $|\Psi\rangle = U|0^n\rangle$. For every vector $\varphi$,
--   $$c_k\varphi = 0 \text{ for all } k = 1,\dots,n \iff \varphi = a\,|\Psi\rangle \text{ for some } a\in\mathbb C.$$
--
--   So $|\Psi\rangle$ is, up to scalars, the only common dark vector of the jump operators $c_k$; for $U = \mathbb 1$ this is the statement $d_k|\varphi\rangle = 0\ \forall k$ iff $|\varphi\rangle \propto |0^n\rangle$.
--
--   **Formalization Note** The page writes "$|\varphi\rangle = U|0^n\rangle$"; the statement holds up to a scalar factor, which is what is formalized.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 4, §IV ("Defining c_k = U d_k U† we have c_k|φ⟩ = 0 iff |φ⟩ = U|0^n⟩ = |Ψ⟩")

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem dark_jumpOps {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (φ : EuclideanSpace ℂ (Fin (2 ^ n))) :
    (∀ k, act (jumpOps U k) φ = 0) ↔ ∃ a : ℂ, φ = a • target U := by sorry

end DissipativePrep.Unique
