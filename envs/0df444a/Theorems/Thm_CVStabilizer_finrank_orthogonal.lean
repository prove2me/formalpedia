-- Prove2me | Theorems.Thm_CVStabilizer_finrank_orthogonal
-- name    : CVStabilizer.finrank_orthogonal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:20:59.775037+00:00
-- url     : https://prove2.me/theorems/65e47dc0-e8a8-417c-a01c-137c302eca2e
-- title:
--   $\dim W^\omega=2n-k$ (with $k\le n$ and $W\subseteq W^\omega$)
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ be linearly independent with $\omega(u_i,u_j)=0$ for all $i,j$, and $W=\operatorname{span}\{u_i\}$. Then $k\le n$, $W\subseteq W^\omega$, and
--
--   $$
--   \dim W^\omega=\dim\mathbb R^{2n}-\dim W=2n-k .
--   $$
--
--   This dimension count is the first step in showing that the code carries $n-k$ logical modes.
--
--   Differences from the source:
--   - reading: k vectors u₁, …, u_k with ω(uᵢ, uⱼ) = 0, and dim W = k used in 'dim W^ω = dim ℝ²ⁿ − dim W = 2n − k' → LinearIndependent ℝ u; reason: the page uses dim W = k; without independence the claim fails (n = 1, k = 2, u₁ = u₂ = (1, 0): dim W^ω = 1 ≠ 0)
--   - encoding: W^ω = {v : ω(v, uᵢ) = 0 ∀i} → (omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}; reason: equal sets, by antisymmetry and linearity of ω
--   - encoding: n − k logical modes, 2n − k, 2(n − k) → k ≤ n is concluded; natural-number subtraction and index type Fin (n − k); reason: since k ≤ n is proved, the subtractions are the true differences
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column ("It follows that dim W ω = dim R2n −dim W = 2n −k")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **`dim W^ω = 2n − k`**, Barnes, arXiv:quant-ph/0405064v1, p.2: "It follows that
dim W^ω = dim ℝ²ⁿ − dim W = 2n − k". For linearly independent `u₁, …, u_k ∈ ℝ²ⁿ` with
`ω(uᵢ, uⱼ) = 0`, `W = span uᵢ`: `k ≤ n`, `W ⊆ W^ω`, and `dim W^ω = 2n − k`.

**Formalization Note** The page uses `dim W = k`, i.e. that the `uᵢ` are linearly independent;
this is assumed (without it the claim fails: `n = 1`, `k = 2`, `u₁ = u₂ = (1, 0)`). `k ≤ n` is
concluded, so the natural-number subtraction `2n − k` is the true difference. `W^ω` is Mathlib's
`(omega n).orthogonal W`. -/
theorem finrank_orthogonal (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hu : LinearIndependent ℝ u) (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    let Wω : Submodule ℝ (PhaseSpace n) := (omega n).orthogonal W
    k ≤ n ∧ W ≤ Wω ∧ Module.finrank ℝ Wω = 2 * n - k := by sorry

end CVStabilizer
