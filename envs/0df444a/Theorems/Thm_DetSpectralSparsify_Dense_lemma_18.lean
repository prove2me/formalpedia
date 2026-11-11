-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_18
-- name    : DetSpectralSparsify.Dense.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:15.175+00:00
-- url     : https://prove2.me/theorems/b317e93e-5c36-4126-bf3f-9e6a4e5b9a2c
-- title:
--   Lemma 18 (Convergence of the exponent) — α_r = 2 + 1/(r + 1/(α₀ − 2)), decreasing to 2, n^{α_r} ≤ e n² for r ≥ ln n
-- statement:
--   Let $(\alpha_r)$ be defined by the recurrence (40), $\alpha_{r+1}=3-1/(\alpha_r-1)$, from a real starting value $\alpha_0>2$ (the paper takes $\alpha_0=\omega$). Then for every $r\ge0$,
--   $$\alpha_r=2+\frac{1}{r+1/(\alpha_0-2)} ,\tag{46}$$
--   $(\alpha_r)_{r\ge0}$ is strictly decreasing with limit $2$, and for every $n$ and every $r\ge\ln n$,
--   $$n^{\alpha_r}\le e\,n^2 .$$
--   For every $\alpha_0\ge2$ the continuous form $\alpha_r=2+\frac{\alpha_0-2}{1+r(\alpha_0-2)}$ holds, $(\alpha_r)$ is non-increasing with limit $2$, and the same bound $n^{\alpha_r}\le en^2$ holds for $r\ge\ln n$.
--
--   The bound turns the $n^{\alpha_r}$ factor of the $r$-level algorithm into $O(n^2)$ when $r=\lceil\ln n\rceil$.
--
--   **Formalization Note** $n^{\alpha_r}$ is the real power `Real.rpow`; $n$ ranges over the naturals (for $n=0$ both sides vanish). $(\alpha_r)$ is the recursively defined `alphaSeq`.
--
--   Differences from the source:
--   - generalization: α₀ = ω, the matrix multiplication exponent → any real α₀ > 2 for (46) and strict decrease, and any α₀ ≥ 2 for the continuous form, the limit and the bound; reason: ω is not known to exceed 2, and (46) divides by ω − 2; the statement specializes to α₀ = ω whenever ω > 2 and covers ω = 2 through the continuous form
--   - encoding: (α_r) decreases to 2 → StrictAnti (resp. Antitone at α₀ = 2) and convergence to 2; reason: the same statement in Mathlib's vocabulary
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.30, Lemma 18; recurrence (40), p.28

import Definitions.Def_DetSpectralSparsify_Dense_MatrixChernoff

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 18 (Convergence of the exponent), p.30, for the recurrence (40) started at any real
`α₀ > 2` in place of `ω`: `α_r = 2 + 1/(r + 1/(α₀ - 2))` for every `r ≥ 0` (46); `(α_r)` is
strictly decreasing with limit `2`; and `n^{α_r} ≤ e n²` whenever `r ≥ ln n`. The continuous form
`α_r = 2 + (α₀ - 2)/(1 + r(α₀ - 2))`, the limit, monotonicity and the bound also hold at
`α₀ = 2`. -/
theorem lemma_18 :
    (∀ α₀ : ℝ, 2 < α₀ →
      (∀ r : ℕ, alphaSeq α₀ r = 2 + 1 / (r + 1 / (α₀ - 2))) ∧
      StrictAnti (alphaSeq α₀) ∧
      Filter.Tendsto (alphaSeq α₀) Filter.atTop (nhds 2) ∧
      ∀ (n r : ℕ), Real.log n ≤ r → (n : ℝ) ^ alphaSeq α₀ r ≤ Real.exp 1 * (n : ℝ) ^ 2) ∧
    (∀ α₀ : ℝ, 2 ≤ α₀ →
      (∀ r : ℕ, alphaSeq α₀ r = 2 + (α₀ - 2) / (1 + r * (α₀ - 2))) ∧
      Antitone (alphaSeq α₀) ∧
      Filter.Tendsto (alphaSeq α₀) Filter.atTop (nhds 2) ∧
      ∀ (n r : ℕ), Real.log n ≤ r → (n : ℝ) ^ alphaSeq α₀ r ≤ Real.exp 1 * (n : ℝ) ^ 2) := by sorry

end DetSpectralSparsify.Dense
