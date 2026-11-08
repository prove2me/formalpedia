-- Prove2me | Theorems.Thm_EuclidDiamStream_rank_band_bound
-- name    : EuclidDiamStream.rank_band_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:17.944195+00:00
-- url     : https://prove2.me/theorems/24c035c2-c681-4526-9ebf-3e40df36fdd3
-- title:
--   §3.1, p.11 — $s^2\gtrsim2^d/\|M\|_{\mathrm{op}}$ for every $M$ equal to $1$ outside the balls
-- statement:
--   Let $f:\{0,1\}^d\to\mathbb R^s$ be $(\delta,\tau)$-ball-subspace-evading with $\delta\in(0,1/2)$, and let $M$ be any $2^d\times2^d$ matrix with $M_{z,x}=1$ whenever $z\notin\mathcal B(x,\tau)$. Then
--   $$\frac{\sqrt{1-2\delta}}{2}\cdot2^d\le s^2\,\|M\|_{\mathrm{op}}.$$
--
--   This reduces the main lemma to exhibiting one matrix $M$ of small spectral norm.
--
--   **Formalization Note** The norm is the $\ell_2$ operator norm. The inequality is written without a division, so it also covers $M=0$.
--
--   Differences from the source:
--   - reading: s² ≳ max{2^d/‖M‖_op : M_{z,x} = 1 whenever z ∉ B(x,τ)} → for every such M, (√(1 − 2δ)/2)·2^d ≤ s²‖M‖; reason: the hidden constant follows from the chain on p.11 and the constant 1/4 of Lemma 3.5; every M is the same as the maximum over M, and the source's maximum may be unattained
--   - encoding: ‖M‖_op → ‖M‖ with Matrix.Norms.L2Operator; reason: Mathlib's default matrix norm is entrywise; the scoped instance is the ℓ2 operator norm
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.11, §3.1, display after the proof of Lemma 3.5

import Mathlib
import Definitions.Def_EuclidDiamStream_IsBallSubspaceEvading

open scoped Matrix.Norms.L2Operator

namespace EuclidDiamStream

/-- The lower bound on `s²` displayed after the proof of Lemma 3.5 in §3.1 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.11: for
`f : {0,1}^d → ℝ^s` that is `(δ,τ)`-ball-subspace-evading, `δ ∈ (0,1/2)`, and every `2^d × 2^d` matrix `M` with
`M_{z,x} = 1` whenever `z ∉ B(x,τ)`, `s² ≳ 2^d/‖M‖_op`.

**Formalization Note.** `‖M‖` is the `ℓ2` operator norm (`Matrix.Norms.L2Operator`), not Mathlib's default
entrywise norm. The hidden constant is the explicit `√(1 − 2δ)/2`, which follows from the chain on p.11 and the
constant `1/4` of Lemma 3.5. The inequality is written without dividing by `‖M‖`, which also covers `M = 0`. -/
theorem rank_band_bound (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (d τ s : ℕ) (f : Cube d → (Fin s → ℝ))
    (hf : IsBallSubspaceEvading δ τ f) (M : Matrix (Cube d) (Cube d) ℝ)
    (hM : ∀ x z, τ < ham x z → M z x = 1) :
    Real.sqrt (1 - 2 * δ) / 2 * 2 ^ d ≤ (s : ℝ) ^ 2 * ‖M‖ := by sorry

end EuclidDiamStream
