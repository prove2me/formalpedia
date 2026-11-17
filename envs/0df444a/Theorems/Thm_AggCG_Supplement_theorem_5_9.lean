-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_5_9
-- name    : AggCG.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:29:11.015807+00:00
-- url     : https://prove2.me/theorems/c74bc92f-55f2-4955-93e2-19ae284be074
-- title:
--   Theorem 5.9 — expected Gaussian-smoothed Lasso path length
-- statement:
--   There is an absolute constant $C>0$ such that, for $n\ge d\ge2$, $0<\sigma\le1$, fixed $\lVert y\rVert_2=1$, deterministic $\lVert\bar X\rVert_{\rm op}\le1$, and independent $G_{ij}\sim N(0,\sigma^2/n)$, the number $K(\bar X+G,y)$ of nondegenerate linear segments of the entire positive Lasso path satisfies
--
--   $$
--   \mathbb E K(\bar X+G,y)\le C\frac{nd^{5/2}}{\sigma^2}\left(1+\log\frac{nd}{\sigma}\right).
--   $$
--
--   Differences from the source:
--   - encoding: $\lVert\bar X\rVert_{\rm op}\le1$ and an ordinary expectation of a segment count → a squared Euclidean norm inequality for every vector and a lower Lebesgue integral of an $\mathbb N\cup\{\infty\}$-valued count, with measurability asserted; reason: these are equivalent on the stated finite-dimensional Gaussian model and avoid a junk value for a nonmeasurable count
--   - encoding: the Lasso solution is unique almost surely under the Gaussian design → `lassoPath` is the unique minimizer when one exists and is zero on the singular null event; reason: this makes the path total without changing the expectation or any full-rank instance
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 5.9, p.10, PDF p.11

import Mathlib
import Definitions.Def_AggCG_Supplement_lassoPath

namespace AggCG.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 5.9** (Smoothed Lasso path length; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.10, PDF p.11). There is an absolute constant `C` such that for all
`n ≥ d ≥ 2`, `0 < σ ≤ 1`, every fixed `y ∈ ℝ^n` with `‖y‖₂ = 1` and every deterministic `X̄ ∈ ℝ^{n×d}`
with `‖X̄‖_op ≤ 1`, if `X = X̄ + G` with independent `G_{ij} ∼ N(0, σ²/n)`, then the expected number
`K(X, y)` of nondegenerate linear segments of the scalar Lasso regularization path satisfies
`E K(X, y) ≤ C (n d^{5/2}/σ²)(1 + log(nd/σ))`.

**Formalization Note** `‖X̄‖_op ≤ 1` is stated as `‖X̄v‖₂ ≤ ‖v‖₂` for all `v`. The expectation is the
lower Lebesgue integral of the `ℕ∞`-valued count against the product Gaussian law of `G`, and almost-sure
measurability of the count is part of the claim. -/
theorem theorem_5_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ), 2 ≤ d → d ≤ n → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ∀ (y : Fin n → ℝ), ∑ i, y i ^ 2 = 1 →
      ∀ (Xbar : Matrix (Fin n) (Fin d) ℝ), (∀ v : Fin d → ℝ, ∑ i, (Xbar.mulVec v i) ^ 2 ≤ ∑ j, v j ^ 2) →
        AEMeasurable (fun G : Fin n × Fin d → ℝ =>
            ((lassoSegmentCount (Xbar + Matrix.of fun i j => G (i, j)) y : ℕ∞) : ENNReal))
          (Measure.pi fun _ : Fin n × Fin d => gaussianReal 0 ⟨σ ^ 2 / n, by positivity⟩) ∧
        ∫⁻ G, ((lassoSegmentCount (Xbar + Matrix.of fun i j => G (i, j)) y : ℕ∞) : ENNReal)
            ∂(Measure.pi fun _ : Fin n × Fin d => gaussianReal 0 ⟨σ ^ 2 / n, by positivity⟩) ≤
          ENNReal.ofReal (C * ((n : ℝ) * (d : ℝ) ^ ((5 : ℝ) / 2) / σ ^ 2) *
            (1 + Real.log ((n : ℝ) * d / σ))) := by sorry

end AggCG.Supplement
