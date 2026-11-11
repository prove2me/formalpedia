-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_22
-- name    : CompactRouting.Labeled.lemma_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:38.449787+00:00
-- url     : https://prove2.me/theorems/dfeb4950-fc83-41a2-911d-dab8cb15dddf
-- title:
--   Lemma 22 — some level has $2x_i+2H\Pr_\nu[\theta\ge\delta_i]\le2\tau m$
-- statement:
--   Let $\tau\ge1$ and let $x_0,\dots,x_\tau$, $y_0,\dots,y_\tau$ be real numbers with the properties of Lemma 21 ($H=y_\tau$, $\delta_i=y_{i+1}-x_i$). Let $\nu$ be a probability distribution on a finite subset of $[1,\infty)$ with mean $m$, quantile function $f$ and tail $\bar F$, and let $C,r,\varphi,\Psi$ be as in §B.1. Then
--   $$\min_{i\in[\tau]}\big(2x_i+2H\Pr_{\theta\sim\nu}[\theta\ge\delta_i]\big)\le2\tau m.$$
--   Via LP duality this is the dual form of Lemma 10.
--
--   Differences from the source:
--   - generalization: the normalized heights x_i = h_i(u)/M, y_i = h_i(v)/M of a fixed pair u, v → any real sequences x, y with the properties of Lemma 21 (`NormalizedHeights x y τ`); reason: by Lemma 21 the normalized heights have these properties, so the statement specializes to the paper's
--   - encoding: min over i ∈ [τ] of the expression ≤ 2τm → ∃ i < τ with the expression ≤ 2τm; reason: the minimum of a finite nonempty set is at most b iff some element is
--   - encoding: a distribution ν on a finite subset of [1, ∞); f, C as minima; Ψ as an integral → a finite set S ⊆ [1, ∞) with nonnegative weights summing to 1; f and C as real infima of finite nonempty sets; Ψ as a lower Lebesgue integral in [0, ∞]; reason: Lean convention; same values
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 36, Lemma 22

import Mathlib
import Definitions.Def_CompactRouting_Labeled_LevelLP
import Definitions.Def_CompactRouting_Labeled_Quantile

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 36, Lemma 22: "For every distribution ν on a finite subset of
[1, ∞) with mean m, min_{i∈[τ]} (2x_i + 2H Pr_{θ∼ν}[θ ≥ δ_i]) ≤ 2τm."
`x, y` are any heights with the properties of Lemma 21, `H = y_τ`, `δ_i = y_{i+1} − x_i`; the
minimum over the finite set `[τ]` is at most `2τm` iff some level attains a value at most `2τm`. -/
theorem lemma_22 (x y : ℕ → ℝ) (τ : ℕ) (hN : NormalizedHeights x y τ) (ν : FinDistGeOne) :
    ∃ i < τ, 2 * x i + 2 * y τ * ν.tail (y (i + 1) - x i) ≤ 2 * (τ : ℝ) * ν.mean := by sorry

end CompactRouting.Labeled
