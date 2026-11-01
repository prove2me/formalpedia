-- Prove2me | Theorems.Thm_CVStabilizer_finrank_quotient
-- name    : CVStabilizer.finrank_quotient
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:07.513469+00:00
-- url     : https://prove2.me/theorems/4c19dd1e-2baf-48d2-b7d5-999f8b5e84cf
-- title:
--   $\dim W^\omega/W=2(n-k)$
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ be linearly independent with $\omega(u_i,u_j)=0$ for all $i,j$, and $W=\operatorname{span}\{u_i\}\subseteq W^\omega$. Then
--
--   $$
--   \dim W^\omega/W=\dim W^\omega-\dim W=2(n-k).
--   $$
--
--   The quotient $W^\omega/W$ corresponds to $N(S)/S$, the group of operators acting nontrivially on the code space.
--
--   **Formalization Note** The quotient is $W^\omega$ modulo $W$ viewed inside $W^\omega$.
--
--   Differences from the source:
--   - reading: k vectors u₁, …, u_k with ω(uᵢ, uⱼ) = 0, and dim W = k used in 'dim W^ω = dim ℝ²ⁿ − dim W = 2n − k' → LinearIndependent ℝ u; reason: the page uses dim W = k; without independence the claim fails (n = 1, k = 2, u₁ = u₂ = (1, 0): dim W^ω = 1 ≠ 0)
--   - encoding: W^ω = {v : ω(v, uᵢ) = 0 ∀i} → (omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}; reason: equal sets, by antisymmetry and linearity of ω
--   - encoding: n − k logical modes, 2n − k, 2(n − k) → k ≤ n is concluded; natural-number subtraction and index type Fin (n − k); reason: since k ≤ n is proved, the subtractions are the true differences
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column ("so that the group N(S)/S of operators acting nontrivially on the code space corresponds to a subspace of dimension dim W ω/W = dim W ω −dim W = 2(n−k)")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **`dim W^ω/W = 2(n − k)`**, Barnes, arXiv:quant-ph/0405064v1, p.2: "so that the group N(S)/S of
operators acting nontrivially on the code space corresponds to a subspace of dimension
dim W^ω/W = dim W^ω − dim W = 2(n−k)." For linearly independent `u₁, …, u_k` with
`ω(uᵢ, uⱼ) = 0` and `W = span uᵢ ⊆ W^ω`, the quotient `W^ω/W` has dimension `2(n − k)`.

**Formalization Note** The quotient is `W^ω ⧸ (W ∩ W^ω)` with `W` pulled back to `W^ω`
(`W.comap Wω.subtype`); since `W ⊆ W^ω` this is `W^ω/W`. Linear independence is assumed as in
`finrank_orthogonal`. -/
theorem finrank_quotient (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hu : LinearIndependent ℝ u) (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    let Wω : Submodule ℝ (PhaseSpace n) := (omega n).orthogonal W
    Module.finrank ℝ (Wω ⧸ W.comap Wω.subtype) = 2 * (n - k) := by sorry

end CVStabilizer
