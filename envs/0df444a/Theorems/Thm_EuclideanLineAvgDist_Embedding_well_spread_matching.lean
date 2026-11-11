-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_well_spread_matching
-- name    : EuclideanLineAvgDist.Embedding.well_spread_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:57.862614+00:00
-- url     : https://prove2.me/theorems/efba6937-aa04-437d-93c7-7cc0b457ecca
-- title:
--   Corollary 2.2 — expected matching weight between the extreme sets of a Gaussian projection
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $X\subset\mathbb R^k$ be a set of $n$ points and $\Delta=\frac1{n^2}\sum_{x,y\in X}\|x-y\|_2$. Assume that
--   $$|B(x,\Delta/4)|<\frac n{64}\qquad\text{for every }x\in X,$$
--   where $B(x,r)=\{y\in X:\|x-y\|_2<r\}$. For $g\in\mathbb R^k$ let $X_g^-,X_g^+\subset X$ be the $\lceil n/64\rceil$ smallest and largest points in the ordering given by $x\mapsto\langle x,g\rangle$ (ties broken by any fixed injective labelling of $X$), and let $|A_g|$ be the minimum total Euclidean weight of a perfect matching between $X_g^-$ and $X_g^+$. Then
--   $$\mathbb E_{\gamma\sim N(0,I_k)}|A_\gamma|\;\ge\;c\cdot n\cdot\Delta\sqrt{\frac{\log\log n}{\log n}}.$$
--
--   This is the "well-spread" case of the proof of Theorem 1.1: a direction whose extreme sets are far apart in matching distance. The paper's proof (pp. 12–14) gives $c=1/(64\cdot8192\sqrt{C})$ with $C=4(3+2\log2)$ the constant of Lemma 2.1.
--
--   **Formalization Note** The labelling only affects directions with coinciding projections, a Gaussian-null set when $k\ge1$; the statement holds for every labelling, with one constant. The expectation is a lower Lebesgue integral in $[0,\infty]$. Under the hypothesis, a nonempty $X$ has either $n=1$ (then $\Delta=0$ and both sides vanish) or $n>64$, so the logarithms are positive whenever the right side is nonzero.
--
--   Differences from the source:
--   - encoding: "for a universal constant $c>0$" → $\exists c>0$ placed before all of $k$, $X$ and the tie-breaking labelling; reason: the meaning of a universal constant
--   - reading: $B(x,\Delta/4)$, open or closed not specified → the open ball; reason: the source does not fix the convention; the same open ball as in Lemma 1.7
--   - encoding: $X_g^\pm$ for nonzero $g$, coincidences ignored → $X_g^\pm$ defined for every $g$ with ties broken by a fixed injective labelling, for every such labelling; reason: the source ignores the measure-zero events where projections coincide (p. 12); the integrand changes only on a Gaussian-null set
--   - encoding: $|A_g|$ for a chosen minimum-weight matching → the minimum weight over all bijections $X_g^-\to X_g^+$; reason: every minimum-weight matching has this weight
--   - encoding: $\mathbb E|A_\gamma|$ → lower Lebesgue integral of $|A_g|$ in $[0,\infty]$; reason: the integrand is nonnegative; same value
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 5, Corollary 2.2

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Projection

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Corollary 2.2 (p. 5). There is a universal constant `c > 0` such that for every `k`, every set
`X ⊂ ℝᵏ` of `n` points with `Δ = (1/n²) ∑_{x,y} ‖x - y‖₂` and `|B(x, Δ/4)| < n/64` for every
`x ∈ X`, and every tie-breaking labelling of `X`,
`E_{γ ∼ N(0,I_k)} |A_γ| ≥ c · n · Δ · √(log log n / log n)`, where `|A_g|` is the minimum total
Euclidean weight of a perfect matching between the `⌈n/64⌉` smallest and the `⌈n/64⌉` largest
points of `X` in the order `x ↦ ⟨x, g⟩`. -/
theorem well_spread_matching :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (X : Finset (Eucl k)) (tie : X → ℕ), Function.Injective tie →
      (∀ x : X, ((ball x (avgDist X / 4)).card : ℝ) < (X.card : ℝ) / 64) →
        ENNReal.ofReal (c * (X.card : ℝ) * avgDist X *
            Real.sqrt (Real.log (Real.log (X.card : ℝ)) / Real.log (X.card : ℝ)))
          ≤ expectedExtremeMatching X tie := by sorry

end EuclideanLineAvgDist.Embedding
