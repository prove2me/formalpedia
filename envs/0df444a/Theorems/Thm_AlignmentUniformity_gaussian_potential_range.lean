-- Prove2me | Theorems.Thm_AlignmentUniformity_gaussian_potential_range
-- name    : AlignmentUniformity.gaussian_potential_range
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:30:00.571665+00:00
-- url     : https://prove2.me/theorems/a8caa8b7-e043-4313-9d05-21f8e704f363
-- title:
--   Proposition 3: range of the expected pairwise Gaussian potential
-- statement:
--   Let $d\ge0$ and $t>0$. Over the Borel probability measures $\mu$ on $S^d$, the expected pairwise Gaussian potential
--
--   $$I_{G_t}[\mu]=\int_{S^d}\int_{S^d}G_t(u,v)\,d\mu(v)\,d\mu(u)$$
--
--   has range exactly $\big[e^{-2t}\,{}_0F_1(;\tfrac{d+1}{2};t^2),\,1\big]$. Moreover:
--
--   1. The minimum $e^{-2t}{}_0F_1(;\frac{d+1}{2};t^2)$ is attained if and only if $\mu=\sigma_d$.
--   2. As a function of $d$, the minimum strictly decreases and converges to $e^{-2t}$ as $d\to\infty$.
--   3. The maximum $1$ is attained if and only if $\mu=\delta_u$ for some $u\in S^d$.
--
--   Here ${}_0F_1(;\alpha;z)=\sum_{n\ge0}z^n/((\alpha)_nn!)$.
--
--   The proposition gives the optimal value of the uniformity loss in closed form.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Appendix A.1.1, Proposition 3, eq. (5), pp. 15-17

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem gaussian_potential_range (d : ℕ) {t : ℝ} (ht : 0 < t) :
    {I : ℝ | ∃ μ : Measure (Vec (d + 1)), IsSphereProb μ ∧ energy (gaussKernel t) μ μ = I} =
        Set.Icc (Real.exp (-2 * t) * hyp0F1 (((d : ℝ) + 1) / 2) (t ^ 2)) 1 ∧
      (∀ μ : Measure (Vec (d + 1)), IsSphereProb μ →
        (energy (gaussKernel t) μ μ = Real.exp (-2 * t) * hyp0F1 (((d : ℝ) + 1) / 2) (t ^ 2) ↔
          μ = sphereUnif (d + 1))) ∧
      StrictAnti (fun d' : ℕ => Real.exp (-2 * t) * hyp0F1 (((d' : ℝ) + 1) / 2) (t ^ 2)) ∧
      Tendsto (fun d' : ℕ => Real.exp (-2 * t) * hyp0F1 (((d' : ℝ) + 1) / 2) (t ^ 2)) atTop
        (𝓝 (Real.exp (-2 * t))) ∧
      (∀ μ : Measure (Vec (d + 1)), IsSphereProb μ →
        (energy (gaussKernel t) μ μ = 1 ↔
          ∃ u ∈ Metric.sphere (0 : Vec (d + 1)) 1, μ = Measure.dirac u)) := by sorry

end AlignmentUniformity
