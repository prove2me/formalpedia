-- Prove2me | Theorems.Thm_CompactRouting_Labeled_claim_22_1
-- name    : CompactRouting.Labeled.claim_22_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:50.822861+00:00
-- url     : https://prove2.me/theorems/475c2032-32fb-4382-b46f-4225714f536a
-- title:
--   Claim 22.1 — $\Psi(x_j)\le j$ for $0\le j<\tau$
-- statement:
--   Let $\tau\ge1$ and let $x_0,\dots,x_\tau$, $y_0,\dots,y_\tau$ be real numbers with the properties of Lemma 21 ($H=y_\tau$, $\delta_i=y_{i+1}-x_i$). Let $\nu$ be a probability distribution on a finite subset of $[1,\infty)$ with mean $m$, quantile function $f$ and tail $\bar F$, and let $C,r,\varphi,\Psi$ be as in §B.1. Assume $C>2\tau$ (the case of the proof of Lemma 22 in which the claim is made). Then
--   $$\Psi(x_j)\le j\qquad(0\le j<\tau).$$
--
--   Differences from the source:
--   - generalization: the normalized heights x_i = h_i(u)/M, y_i = h_i(v)/M of a fixed pair u, v → any real sequences x, y with the properties of Lemma 21 (`NormalizedHeights x y τ`); reason: by Lemma 21 the normalized heights have these properties, so the statement specializes to the paper's
--   - encoding: a distribution ν on a finite subset of [1, ∞); f, C as minima; Ψ as an integral → a finite set S ⊆ [1, ∞) with nonnegative weights summing to 1; f and C as real infima of finite nonempty sets; Ψ as a lower Lebesgue integral in [0, ∞]; reason: Lean convention; same values
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 37, Claim 22.1 (in the proof of Lemma 22, p. 36)

import Mathlib
import Definitions.Def_CompactRouting_Labeled_LevelLP
import Definitions.Def_CompactRouting_Labeled_Quantile

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 37, Claim 22.1 (in the proof of Lemma 22, case `C > 2τ`):
"Ψ(x_j) ≤ j (0 ≤ j < τ)."
`x, y` are any heights with the properties of Lemma 21 (`H = y_τ`), `ν` a distribution on a
finite subset of `[1, ∞)`, `C`, `r`, `φ`, `Ψ` as on p. 36 (`Cval`, `rr`, `phi`, `Psi`). -/
theorem claim_22_1 (x y : ℕ → ℝ) (τ : ℕ) (hN : NormalizedHeights x y τ) (ν : FinDistGeOne)
    (hC : 2 * (τ : ℝ) < Cval x y τ ν) :
    ∀ j < τ, Psi x y τ ν (x j) ≤ (j : ENNReal) := by sorry

end CompactRouting.Labeled
