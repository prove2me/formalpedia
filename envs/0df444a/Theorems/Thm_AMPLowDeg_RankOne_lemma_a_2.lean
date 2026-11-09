-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_2
-- name    : AMPLowDeg.RankOne.lemma_a_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:38.189725+00:00
-- url     : https://prove2.me/theorems/5db69db4-1c78-4e6d-aac4-93e90532cd66
-- title:
--   Lemma A.2 — Hermite form of Gaussian integration by parts
-- statement:
--   Let $k\ge0$ and let $f:\mathbb R\to\mathbb R$ be $k$ times continuously differentiable. Suppose that $f$ and its first $k$ derivatives are bounded by $\exp(O(|y|^a))$ for some $a\in(0,2)$. Then, with $h_k$ the orthonormal probabilists' Hermite polynomial and $y\sim\mathcal N(0,1)$,
--
--   $$
--   \mathbb E\big[h_k(y)f(y)\big]=\frac{1}{\sqrt{k!}}\,\mathbb E\big[f^{(k)}(y)\big].
--   $$
--
--   The identity computes Hermite coefficients by differentiation; it gives the coefficients (3.2) of a polynomial in the Gaussian noise and the Gaussian integrations by parts in §§4 and 6.
--
--   Differences from the source:
--
--   - reading: f(y) and its first k derivatives are bounded by exp(O(|y|^α)) for some α ∈ (0, 2) → ∃ a ∈ (0, 2), ∃ C, ∀ j ≤ k, ∀ y, |f^{(j)}(y)| ≤ C·exp(C·|y|^a); reason: the standard meaning of the O-bound; since the derivatives are continuous, a bound for large |y| and a bound for all y are equivalent
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 21, Lemma A.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Cumulant

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma A.2, p. 21 — Hermite form of Gaussian integration by parts: if `f` is `k` times
continuously differentiable and `f` and its first `k` derivatives are bounded by
`exp(O(|y|^a))` for some `a ∈ (0, 2)`, then `E[h_k(y) f(y)] = E[f^{(k)}(y)] / √(k!)` for
`y ∼ 𝒩(0, 1)`, with `h_k` the orthonormal probabilists' Hermite polynomial. -/
theorem lemma_a_2 (k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ k f)
    (hgrowth : ∃ a : ℝ, 0 < a ∧ a < 2 ∧ ∃ C : ℝ, ∀ j ≤ k, ∀ y : ℝ,
      |iteratedDeriv j f y| ≤ C * Real.exp (C * |y| ^ a)) :
    ∫ y, hermNorm k y * f y ∂(gaussianReal 0 1) =
      (1 / Real.sqrt (k.factorial)) * ∫ y, iteratedDeriv k f y ∂(gaussianReal 0 1) := by sorry

end AMPLowDeg.RankOne
