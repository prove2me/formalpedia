-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_corollary_6_6
-- name    : BQPNotInIP.OracleSep.corollary_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:46.155085+00:00
-- url     : https://prove2.me/theorems/71ea28a3-0ddc-4fad-b37f-ad32f68d708b
-- title:
--   Corollary 6.6 — removing independent Gaussian noise
-- statement:
--   Let $m\ge1$ and $F:\mathbb R^m\to\mathbb R$ be smooth and convex. On the cube $[-1,1]^m$, assume $\|\nabla F\|_1\le L$ and $\|\nabla^2F\|_1\le K$, with $L\le m$. Let $D\sim\mathcal N(0,\Sigma)$ have unit coordinate variances, and let $Z\sim\mathcal N(0,I_m)$ be independent of $D$. Choose a nonnegative $\beta$ with $|\Sigma_{ij}|\le\beta$ whenever $i\ne j$. Singular covariance is allowed.
--
--   For every $0<\delta\le1/2$ and every integer $T\ge0$,
--   $$
--   \left|\mathbb E F(\operatorname{sgn}D)-\mathbb E F(\operatorname{sgn}Z)\right|
--   \le T\left(400L\delta\sqrt{\ln(2m)}+\frac{\beta K}{4\delta^2}+\frac4{m^{48}}\right)
--   +2^{-T/2}mL.
--   $$
--   The bound includes $T=0$ and does not require positive-definite covariance. It compares the original Gaussian signs directly to independent signs, rather than leaving a fixed amount of independent noise.
--
--   Differences from the source:
--   - encoding: a nonempty coordinate range [m] in logarithms and maxima → 0 < m; reason: the displayed logarithms and maxima presuppose a positive dimension
--   - encoding: real vectors, smooth functions, Gaussian expectations and suprema of derivative norms → coordinates indexed by Fin m, C∞ expressed as ContDiff ℝ (⊤ : ℕ∞), entrywise sums of coordinate derivatives, and pointwise bounds on the stated domains; reason: these are the same finite-dimensional objects and avoid default-valued real suprema
--   - encoding: independent centered Gaussian vectors with the stated covariances → the product of their canonical Gaussian laws, with positive-semidefinite covariance explicitly required; reason: expectations depend only on these laws; positive semidefiniteness is implied by being a covariance, and singular covariances remain allowed
--   - generalization: β is the maximum absolute off-diagonal covariance → any nonnegative upper bound β on every absolute off-diagonal covariance; reason: the right side is monotone in β since the Hessian bound K is nonnegative; choosing the maximum recovers the printed result, with β = 0 for m = 1
--   - encoding: Gaussian sign rounding → Real.sign, with sign zero equal to zero; reason: every rounded coordinate has positive variance, so zero has probability zero
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Corollary 6.6, PDF p. 20 (printed p. 18). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=20

import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem corollary_6_6 {m : ℕ} (hm : 0 < m) (F : RVec m → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : ConvexOn ℝ Set.univ F)
    (L K : ℝ) (hgrad : ∀ x ∈ cube m, gradientL1 F x ≤ L)
    (hhess : ∀ x ∈ cube m, hessianL1 F x ≤ K) (hL : L ≤ m)
    (cov : Matrix (Fin m) (Fin m) ℝ) (hcov : cov.PosSemidef)
    (hdiag : ∀ i, cov i i = 1) (β : ℝ) (hβ : 0 ≤ β)
    (hoff : ∀ i j, i ≠ j → |cov i j| ≤ β)
    (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ (1:ℝ)/2) (T : ℕ) :
    |(∫ z, F (signs z.2) ∂(gaussianPair 1 cov)) -
      (∫ z, F (signs z.1) ∂(gaussianPair 1 cov))| ≤
      T * comparisonError m L K β δ + Real.rpow 2 (-(T:ℝ)/2) * m * L := by sorry

end BQPNotInIP.OracleSep
