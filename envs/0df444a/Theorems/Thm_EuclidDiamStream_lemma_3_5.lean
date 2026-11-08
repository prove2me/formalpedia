-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_5
-- name    : EuclidDiamStream.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:14.913858+00:00
-- url     : https://prove2.me/theorems/8e44e1ee-eb7e-4bba-8971-1da899078731
-- title:
--   Lemma 3.5 — a $[0,1]$ matrix of rank $\le s^2$ vanishing on Hamming balls, with large Frobenius norm
-- statement:
--   Let $f:\{0,1\}^d\to\mathbb R^s$ be $(\delta,\tau)$-ball-subspace-evading, with $\delta\in(0,1/2)$. Then there is a matrix $B\in[0,1]^{2^d\times2^d}$ of rank at most $s^2$ with $B_{x,z}=0$ for every $z\in\mathcal B(x,\tau)$ and
--   $$\|B\|_F^2\ge\frac{(1-2\delta)4^d}{4s^2}.$$
--
--   The lemma creates an average margin from a rank bound, and the rest of the proof of Lemma 3.4 plays this margin against a matrix of small spectral norm.
--
--   Differences from the source:
--   - reading: Ω((1 − 2δ)4^d/s²) → the explicit constant 1/4; reason: the proof gives (1 − ε)(1 − 2δ)4^d/(2m) for every ε > 0 with m ≤ s² (pp.10–11), so ε = 1/4 leaves room for the limit; an absolute constant is what Ω means here
--   - encoding: the context f of §3.1 with δ ∈ (0,1/2) → explicit hypotheses 0 < δ < 1/2 and IsBallSubspaceEvading δ τ f; reason: the page's standing assumptions (p.9)
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.9, Lemma 3.5; proof pp.9–11

import Mathlib
import Definitions.Def_EuclidDiamStream_IsBallSubspaceEvading

namespace EuclidDiamStream

/-- Lemma 3.5 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.9: for `f : {0,1}^d → ℝ^s` that is `(δ,τ)`-ball-subspace-evading, `δ ∈ (0,1/2)`, there is
a matrix `B ∈ [0,1]^{2^d × 2^d}` of rank at most `s²` with `B_{x,z} = 0` for every `z ∈ B(x,τ)` and
`‖B‖_F² ≥ Ω((1 − 2δ)4^d/s²)`.

**Formalization Note.** The `Ω` constant is the explicit `1/4`, which the proof gives (pp.10–11:
`(1 − ε)(1 − 2δ)4^d/(2m)`, `m ≤ s²`, with room for the limit). The squared Frobenius norm is written as a
double sum. -/
theorem lemma_3_5 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (d τ s : ℕ) (f : Cube d → (Fin s → ℝ))
    (hf : IsBallSubspaceEvading δ τ f) :
    ∃ B : Matrix (Cube d) (Cube d) ℝ,
      (∀ x z, 0 ≤ B x z ∧ B x z ≤ 1) ∧
      B.rank ≤ s ^ 2 ∧
      (∀ x z, ham x z ≤ τ → B x z = 0) ∧
      (1 - 2 * δ) * 4 ^ d / (4 * (s : ℝ) ^ 2) ≤ ∑ x, ∑ z, (B x z) ^ 2 := by sorry

end EuclidDiamStream
