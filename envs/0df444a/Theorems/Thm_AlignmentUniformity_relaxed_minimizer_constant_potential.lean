-- Prove2me | Theorems.Thm_AlignmentUniformity_relaxed_minimizer_constant_potential
-- name    : AlignmentUniformity.relaxed_minimizer_constant_potential
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:31:56.01266+00:00
-- url     : https://prove2.me/theorems/4df9ac1d-9702-46aa-87a3-f8a30df0f636
-- title:
--   Theorem 1 (proof of result 2, step 2): $U_{\mu^*}$ is constant $\mu^*$-a.s. at every minimizer of eq. (13)
-- statement:
--   Let $d\ge0$ and $\tau>0$, and for a Borel probability measure $\mu$ on $S^d$ let $U_\mu(u)=\int_{S^d}e^{u^\top v/\tau}\,d\mu(v)$. Let $\mu^*$ be a minimizer of the relaxed problem
--
--   $$\min_{\mu\in\mathcal{M}(S^d)}\int_{S^d}\log U_\mu(u)\,d\mu(u)\qquad\text{(eq. 13)}.$$
--
--   Then $U_{\mu^*}$ is constant $\mu^*$-almost surely: there is $c\in\mathbb{R}$ with $U_{\mu^*}(u)=c$ for $\mu^*$-almost every $u$.
--
--   This is the second step of the paper's proof that the uniformity term of Theorem 1 is minimized by perfectly uniform encoders.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Appendix A.2, proof of Theorem 1, result 2, step 2, eqs. (12)-(15), pp. 21-23

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem relaxed_minimizer_constant_potential (d : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : Measure (Vec (d + 1))) (hμ : IsSphereProb μ)
    (hmin : ∀ ν : Measure (Vec (d + 1)), IsSphereProb ν →
      relaxedObjective τ μ ≤ relaxedObjective τ ν) :
    ∃ c : ℝ, ∀ᵐ u ∂μ, expPotential τ μ u = c := by sorry

end AlignmentUniformity
