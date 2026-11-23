-- Prove2me | Theorems.Thm_AlignmentUniformity_uniform_unique_energy_minimizer
-- name    : AlignmentUniformity.uniform_unique_energy_minimizer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:28:25.265568+00:00
-- url     : https://prove2.me/theorems/ec0fdbb2-05fe-47c4-b9ff-51710d5c4954
-- title:
--   Proposition 1: $\sigma_d$ uniquely minimizes the expected pairwise Gaussian potential
-- statement:
--   Let $d\ge0$ and $t>0$, and let $\mathcal{M}(S^d)$ be the set of Borel probability measures on $S^d$. Then the uniform distribution $\sigma_d$ is the unique solution of
--
--   $$\min_{\mu\in\mathcal{M}(S^d)}\int_{S^d}\int_{S^d}G_t(u,v)\,d\mu(v)\,d\mu(u).$$
--
--   That is, $\sigma_d\in\mathcal{M}(S^d)$, $I_{G_t}[\sigma_d]\le I_{G_t}[\mu]$ for every $\mu\in\mathcal{M}(S^d)$, and equality forces $\mu=\sigma_d$.
--
--   This is why $\mathcal{L}_{\mathsf{uniform}}$ measures uniformity: among all feature distributions on the sphere, only the uniform one minimizes the expected pairwise Gaussian potential.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Section 4.1.2, Proposition 1, p. 5; restated in Appendix A.1, Proposition 1, eq. (4), p. 14

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem uniform_unique_energy_minimizer (d : ℕ) {t : ℝ} (ht : 0 < t) :
    IsSphereProb (sphereUnif (d + 1)) ∧
      ∀ μ : Measure (Vec (d + 1)), IsSphereProb μ →
        energy (gaussKernel t) (sphereUnif (d + 1)) (sphereUnif (d + 1)) ≤
            energy (gaussKernel t) μ μ ∧
          (energy (gaussKernel t) μ μ =
              energy (gaussKernel t) (sphereUnif (d + 1)) (sphereUnif (d + 1)) →
            μ = sphereUnif (d + 1)) := by sorry

end AlignmentUniformity
