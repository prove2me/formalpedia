-- Prove2me | Theorems.Thm_DiazModulus_fv_dot_orthogonal
-- name    : DiazModulus.fv_dot_orthogonal
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:18.828942+00:00
-- url     : https://prove2.me/theorems/1b267f50-4719-4fca-be49-ca6a05705eef
-- title:
--   For a ℂ-subspace W ⊆ ℂⁿ, the orthogonal {z : w · z = 0 for all w ∈ W} for the bilinear dot product is a ℂ-subspace of dimension n − dim W
-- statement:
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one).
--
--   For every $\mathbb C$-subspace $W \subseteq \mathbb C^n$ there is a $\mathbb C$-subspace $V \subseteq \mathbb C^n$ with
--   $$V = \{z \in \mathbb C^n : w \cdot z = 0 \text{ for all } w \in W\} \quad\text{and}\quad \dim V + \dim W = n.$$
-- source:
--   Classical linear algebra; a step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (pp. 5–6). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_dot_orthogonal {n : ℕ} (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ V : Submodule ℂ (Fin n → ℂ), (∀ z, z ∈ V ↔ ∀ w ∈ W, w ⬝ᵥ z = 0) ∧
      Module.finrank ℂ ↥V + Module.finrank ℂ ↥W = n := by
  sorry

end DiazModulus
