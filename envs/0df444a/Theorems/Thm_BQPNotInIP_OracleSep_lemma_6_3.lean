-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_lemma_6_3
-- name    : BQPNotInIP.OracleSep.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:50:31.514667+00:00
-- url     : https://prove2.me/theorems/e19d5460-2165-4e78-9cf5-296d8249aa67
-- title:
--   Lemma 6.3 — convexity controls sign-smoothing error
-- statement:
--   Let $m\ge1$ and let $F:\mathbb R^m\to\mathbb R$ be smooth and convex with $\|\nabla F(x)\|_1\le L$ on $[-1,1]^m$. Let $D\sim\mathcal N(0,\Sigma)$ have unit coordinate variances, allowing singular covariance, and let $Z\sim\mathcal N(0,I_m)$ be independent of $D$. For $1/2\le\tau\le1$, set $G=\sqrt\tau Z+\sqrt{1-\tau}D$. For every $a\in\mathbb R^m$ and $0<\delta\le1/2$,
--   $$
--   0\le\mathbb E F(\operatorname{sgn}(a+G))-\mathbb E F(h_{a,\delta}(G))
--   \le18L\delta\left(\|a\|_\infty+\sqrt{\ln(2m)}\right).
--   $$
--   Both the lower and upper bounds are asserted. Only the cube gradient bound is required. The estimate compares a discontinuous rounding operation to a smooth coordinate map without a factor linear in the dimension.
--
--   Differences from the source:
--   - encoding: a nonempty coordinate range [m] in logarithms and maxima → 0 < m; reason: the displayed logarithms and maxima presuppose a positive dimension
--   - encoding: real vectors, smooth functions, Gaussian expectations and suprema of derivative norms → coordinates indexed by Fin m, C∞ expressed as ContDiff ℝ (⊤ : ℕ∞), entrywise sums of coordinate derivatives, and pointwise bounds on the stated domains; reason: these are the same finite-dimensional objects and avoid default-valued real suprema
--   - encoding: independent centered Gaussian vectors with the stated covariances → the product of their canonical Gaussian laws, with positive-semidefinite covariance explicitly required; reason: expectations depend only on these laws; positive semidefiniteness is implied by being a covariance, and singular covariances remain allowed
--   - encoding: Gaussian sign rounding → Real.sign, with sign zero equal to zero; reason: every rounded coordinate has positive variance, so zero has probability zero
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Lemma 6.3, PDF p. 16 (printed p. 14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=16

import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem lemma_6_3 {m : ℕ} (hm : 0 < m) (F : RVec m → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : ConvexOn ℝ Set.univ F)
    (L : ℝ) (hgrad : ∀ x ∈ cube m, gradientL1 F x ≤ L)
    (cov : Matrix (Fin m) (Fin m) ℝ) (hcov : cov.PosSemidef)
    (hdiag : ∀ i, cov i i = 1) (a : RVec m) (τ δ : ℝ)
    (hτ : (1:ℝ)/2 ≤ τ ∧ τ ≤ 1) (hδ : 0 < δ ∧ δ ≤ (1:ℝ)/2) :
    let E := (∫ z, F (signs (a + interpolate τ z)) ∂(gaussianPair 1 cov)) -
      (∫ z, F (smoothSigns a δ (interpolate τ z)) ∂(gaussianPair 1 cov))
    0 ≤ E ∧ E ≤ 18*L*δ*(‖a‖ + Real.sqrt (Real.log (2*m))) := by sorry

end BQPNotInIP.OracleSep
