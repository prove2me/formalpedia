-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_lemma_4_1
-- name    : BQPNotInIP.OracleSep.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:50:02.298012+00:00
-- url     : https://prove2.me/theorems/bf16a35d-297f-44ac-ad73-407f720b358c
-- title:
--   Lemma 4.1 — smart-path derivative identity
-- statement:
--   Let $Z,D$ be independent centered Gaussian vectors in $\mathbb R^m$ with covariance matrices $\Sigma_Z,\Sigma_D$. Let $Q:\mathbb R^m\to\mathbb R$ be smooth, with every coordinate partial derivative of every positive order bounded on the whole space. Define $G(t)=\sqrt t Z+\sqrt{1-t}D$ and $q(t)=\mathbb E Q(G(t))$. For every $0<t<1$, the derivative exists and satisfies
--   $$
--   q'(t)=\frac12\sum_{i,j}\big((\Sigma_Z)_{ij}-(\Sigma_D)_{ij}\big)
--   \mathbb E\big[\partial_{ij}Q(G(t))\big].
--   $$
--   Each derivative has its own uniform bound. The function $Q$ itself need not be bounded. Singular Gaussian covariances are allowed. This is the interpolation identity relating changes in covariance to the Hessian of a test function.
--
--   Differences from the source:
--   - encoding: real vectors, smooth functions, Gaussian expectations and suprema of derivative norms → coordinates indexed by Fin m, C∞ expressed as ContDiff ℝ (⊤ : ℕ∞), entrywise sums of coordinate derivatives, and pointwise bounds on the stated domains; reason: these are the same finite-dimensional objects and avoid default-valued real suprema
--   - encoding: independent centered Gaussian vectors with the stated covariances → the product of their canonical Gaussian laws, with positive-semidefinite covariance explicitly required; reason: expectations depend only on these laws; positive semidefiniteness is implied by being a covariance, and singular covariances remain allowed
--   - reading: any partial derivative of Q is bounded → every coordinate derivative of each positive order has a global bound; reason: this is the literal all-orders reading, without adding a bound on the zeroth derivative
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Lemma 4.1, PDF p. 11 (printed p. 9). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=11

import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem lemma_4_1 {m : ℕ} (covZ covD : Matrix (Fin m) (Fin m) ℝ)
    (hZ : covZ.PosSemidef) (hD : covD.PosSemidef)
    (Q : RVec m → ℝ) (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hbounded : ∀ k : ℕ, 0 < k → ∀ v : Fin k → Fin m,
      ∃ B : ℝ, ∀ x : RVec m,
        |(iteratedFDeriv ℝ k Q x) (fun j => Pi.single (v j) 1)| ≤ B)
    (t : ℝ) (ht : 0 < t ∧ t < 1) :
    HasDerivAt (fun u : ℝ => ∫ z, Q (interpolate u z) ∂(gaussianPair covZ covD))
      ((1:ℝ)/2 * ∑ i, ∑ j, (covZ i j - covD i j) *
        (∫ z, partial₂ Q i j (interpolate t z) ∂(gaussianPair covZ covD))) t := by sorry

end BQPNotInIP.OracleSep
