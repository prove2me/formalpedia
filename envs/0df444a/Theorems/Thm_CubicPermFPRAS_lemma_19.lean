-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_19
-- name    : CubicPermFPRAS.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:39.374412+00:00
-- url     : https://prove2.me/theorems/e57f5fec-f9ac-4831-877c-479d2012e18b
-- title:
--   Lemma 19, p.17 — FAR occupation variance $\le C_\alpha n^2\log(2n)p_v^2/T$ (corrected: $\log(2n)$ for $\log n$)
-- statement:
--   For every $\alpha>1$ there is a constant $C_\alpha>0$, depending only on $\alpha$, such that the following holds. Fix positive activities $\lambda$, a vertex $r\in V_1$ and $\alpha$-rough anchor weights, let $X_0\sim\pi_B$ and let $X_1,X_2,\dots$ evolve by the FAR chain. For every $v\in V_2$, with $p_v=\pi_B(\mathcal N(r,v))$, and every integer $T\ge1$,
--   $$\mathrm{Var}\Big[\frac1T\sum_{t=0}^{T-1}\mathbf 1\{X_t\in\mathcal N(r,v)\}\Big]\le\frac{C_\alpha n^2\log(2n)}{T}\,p_v^2.$$
--
--   With $T$ a large multiple of $n^2\log n$, Chebyshev's inequality turns this into a relative-error-$1/10$ frequency estimate.
--
--   Differences from the source:
--   - correction: $C_\alpha n^2\log n/T$ → $C_\alpha n^2\log(2n)/T$; reason: at $n=1$, $\Omega$ has two states of positive $\pi_B$-mass, so for $T=1$ the variance $p_v(1-p_v)$ is positive while the printed bound is $0$; for $n\ge2$, $\log(2n)\le2\log n$
--   - encoding: the variance of the stationary occupation frequency → $T^{-2}\sum_{s,t<T}\sum_x\pi_B(x)g(x)(P_{\mathrm{FAR}}^{|s-t|}g)(x)$ with $g=\mathbf 1_{\mathcal N(r,v)}-p_v$; reason: the covariance formula for a stationary Markov chain
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 19, p.17 (PDF 19); proof in §6.7

import Mathlib
import Definitions.Def_CubicPermFPRAS_farChain

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 19** (occupation variance for the FAR chain), p.17 (PDF 19), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…) (corrected:
`log(2n)` for `log n`); proved in §6.7.

Fix positive edge activities, a vertex `r ∈ V₁` and `α`-rough anchor weights. Let `X₀ ∼ π_B` and
let `X₁, X₂, …` evolve according to the FAR chain. For every `v ∈ V₂`, with
`p_v = π_B(N(r,v))`, there is `C_α > 0`, depending only on `α`, such that for every integer
`T ≥ 1`, `Var[T⁻¹ ∑_{t<T} 1{X_t ∈ N(r,v)}] ≤ (C_α n² log n / T) p_v²`.

**Formalization Note.** The variance of the stationary occupation frequency is written through
powers of `P_FAR` (`occVar`). The bound is stated with `log(2n)`: at `n = 1`, `Ω` has two states
both of positive `π_B`-mass, so for `T = 1` the variance `p_v(1 − p_v)` is positive while the
printed bound is `0`. For `n ≥ 2`, `log(2n) ≤ 2 log n`. -/
theorem lemma_19 : ∀ α : ℝ, 1 < α → ∃ Cα : ℝ, 0 < Cα ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w → ∀ v : Fin n, ∀ T : ℕ, 1 ≤ T →
      occVar (Bmat lam w) r v T ≤
        Cα * (n : ℝ) ^ 2 * Real.log (2 * n) / T * holeProb (Bmat lam w) r v ^ 2 := by sorry

end CubicPermFPRAS
