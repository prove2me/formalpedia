-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_eq_24_root_sum_bound
-- name    : AdaGradDHS.Diag.eq_24_root_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:22.708061+00:00
-- url     : https://prove2.me/theorems/e3f452e6-0f01-4846-802c-3036f5da1e21
-- title:
--   Eq. (24): $\sum_t a_t^2/\|a_{1:t}\|_2 \le 2\|a_{1:T}\|_2$
-- statement:
--   For every real sequence $a_1, a_2, \dots$ and every $T \in \mathbb{N}$,
--   $$\sum_{t=1}^T \frac{a_t^2}{\|a_{1:t}\|_2} \le 2\,\|a_{1:T}\|_2, \qquad \|a_{1:t}\|_2 = \Big(\sum_{\tau=1}^t a_\tau^2\Big)^{1/2},$$
--   with the convention $0/0 = 0$.
--
--   This scalar inequality, due to Auer and Gentile, is the engine of Lemma 4: applied to each coordinate of the subgradients it bounds the accumulated dual-norm terms of AdaGrad by twice the final accumulated norms.
--
--   **Formalization Note** A zero denominator occurs only when $a_1 = \dots = a_t = 0$, so the numerator is then $0$ too, and Lean's $x/0 = 0$ is the paper's convention.
--
--   Differences from the source:
--   - encoding: ‖a_{1:t}‖₂ with 0/0 = 0 → Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2) with Lean's x / 0 = 0; reason: same quantity; a zero denominator meets only a zero numerator
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Appendix C (proof of Lemma 4), p. 2149, eq. (24)

import Mathlib

namespace AdaGradDHS.Diag

/-- **Eq. (24): `Σ_{t=1}^T a_t² / ‖a_{1:t}‖₂ ≤ 2‖a_{1:T}‖₂`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Appendix C (proof of Lemma 4), p. 2149, eq. (24): "Σ_{t=1}^T a_t² / ‖a1:t‖2 ≤ 2‖a1:T‖2 ,
where we define 0/0 = 0", for "an arbitrary real-valued sequence {ai}".

For every real sequence `a` and every `T`,
`Σ_{t=1}^T a_t² / √(Σ_{τ=1}^t a_τ²) ≤ 2 √(Σ_{τ=1}^T a_τ²)`.

**Formalization Note.** `‖a_{1:t}‖₂` is written `√(Σ_{τ=1}^t a_τ²)`. Lean's `x / 0 = 0` is the
paper's convention `0/0 = 0`; a zero denominator occurs only when `a_1 = ⋯ = a_t = 0`, so the
numerator is then `0` too. -/
theorem eq_24_root_sum_bound (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2) ≤
      2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by sorry

end AdaGradDHS.Diag
