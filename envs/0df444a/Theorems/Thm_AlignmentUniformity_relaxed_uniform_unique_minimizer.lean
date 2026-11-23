-- Prove2me | Theorems.Thm_AlignmentUniformity_relaxed_uniform_unique_minimizer
-- name    : AlignmentUniformity.relaxed_uniform_unique_minimizer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:32:33.946669+00:00
-- url     : https://prove2.me/theorems/68d3d04b-865d-4096-9207-badb666d02fe
-- title:
--   Theorem 1 (proof of result 2, step 3): $\sigma_d$ is the unique minimizer of eq. (13)
-- statement:
--   Let $d\ge0$ and $\tau>0$, and let $U_\mu(u)=\int_{S^d}e^{u^\top v/\tau}\,d\mu(v)$. Then $\sigma_d$ is the unique minimizer of the relaxed problem (eq. 13):
--
--   $$\int_{S^d}\log U_{\sigma_d}\,d\sigma_d\ \le\ \int_{S^d}\log U_\mu\,d\mu\qquad\text{for every }\mu\in\mathcal{M}(S^d),$$
--
--   with equality only if $\mu=\sigma_d$.
--
--   For an encoder $f$, the uniformity term of Theorem 1 equals this objective at the law of $f(x)$, $x\sim p_{\mathrm{data}}$. Result 2 of Theorem 1 follows.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Appendix A.2, proof of Theorem 1, result 2, eq. (13) and step 3, eq. (16), pp. 21-23

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem relaxed_uniform_unique_minimizer (d : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ μ : Measure (Vec (d + 1)), IsSphereProb μ →
      relaxedObjective τ (sphereUnif (d + 1)) ≤ relaxedObjective τ μ ∧
        (relaxedObjective τ μ = relaxedObjective τ (sphereUnif (d + 1)) →
          μ = sphereUnif (d + 1)) := by sorry

end AlignmentUniformity
