-- Prove2me | Theorems.Thm_ContinualCounting_oblivious_lower_bound
-- name    : ContinualCounting.oblivious_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:43.979391+00:00
-- url     : https://prove2.me/theorems/dc2426ec-6abe-43b0-9082-72cb04294b6f
-- title:
--   §5, pp.17, 30 — the oblivious lower bound
-- statement:
--   For all $\varepsilon_0>0$ and $\delta_0<1/3$ there is a constant $c>0$ such that the following holds for every $k$, with $n=16^k$ and $h=\log_2n=4k$. If $\varepsilon\in(0,\varepsilon_0]$, $\delta\in[0,\delta_0]$, $z$ is a noise vector with law $\nu$ on $\mathbb R^n$, and $M(x)=Ax+z$ is $(\varepsilon,\delta)$-DP on $\{0,1\}^n$, then
--   $$\mathbb E\|z\|_\infty\ge\frac{c\,h^{3/2}}{\max\{\varepsilon,\delta\}}.$$
--
--   Combined with Lemma 2 and the restriction to a prefix of length a power of 16, this gives Theorem 1.
--
--   **Formalization Note** The expectation has values in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: "an Ω(log^{3/2} m / max{ε, δ}) for oblivious mechanisms", with no range stated → ∀ ε₀ > 0, ∀ δ₀ < 1/3, ∃ c > 0, for ε ∈ (0, ε₀], δ ∈ [0, δ₀]; reason: a regime is necessary (at δ ≥ 1 zero noise is DP), and it is the regime that three copies (Lemma 4) and Lemma 1 use
--   - encoding: h = log₂ n with n a power of 16 → n = 16^k, h = 4k; reason: the same parameter
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, p.17 (PDF p.18), concluded p.30 (PDF p.31)

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_ContinualCounting_oblivious

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **The oblivious lower bound.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5,
p.17: "We then prove an Ω(log^{3/2} m / max{ε, δ}) for oblivious mechanisms", concluded on p.30 as
`E[∥z∥∞] = Ω(h^{3/2} / max{ε, δ})`, with "We assume n is a power of 16 and let h = log₂ n" (p.17).

**Formalization Note.** `n = 16^k`, so `h = log₂ n = 4k`. The hidden constant depends on bounds `ε₀` of `ε` and
`δ₀ < 1/3` of `δ`: a regime is necessary, since at `δ ≥ 1` the noiseless mechanism is DP, and `δ₀ < 1/3` is what
the three copies of Lemma 4 leave of Lemma 1's range `3δ₀ < 1`. -/
theorem oblivious_lower_bound (ε₀ δ₀ : ℝ) (hε₀ : 0 < ε₀) (hδ₀ : δ₀ < 1 / 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (ε δ : ℝ), 0 < ε → ε ≤ ε₀ → 0 ≤ δ → δ ≤ δ₀ →
      ∀ ν : Measure (Fin (16 ^ k) → ℝ), IsProbabilityMeasure ν →
        IsDP (oblivious ν) ε δ →
        ENNReal.ofReal (c * (4 * (k : ℝ)) ^ ((3 : ℝ) / 2) / max ε δ) ≤ ∫⁻ z, ‖z‖ₑ ∂ν := by sorry

end ContinualCounting
