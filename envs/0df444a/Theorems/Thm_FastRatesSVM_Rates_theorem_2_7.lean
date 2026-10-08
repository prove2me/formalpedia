-- Prove2me | Theorems.Thm_FastRatesSVM_Rates_theorem_2_7
-- name    : FastRatesSVM.Rates.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:21.845836+00:00
-- url     : https://prove2.me/theorems/72173f73-adaa-4ee3-a3d3-745251170864
-- title:
--   Theorem 2.7 — Gaussian RKHS approximation under geometric noise
-- statement:
--   Let $X$ be the closed unit ball in $\mathbb R^d$, $\sigma>0$, and let the distribution have geometric noise exponent $\alpha>0$ with constant $C$ in (8). There is a constant $c_d>0$ depending only on $d$ such that, for every $\lambda>0$,
--   $$
--   a_\sigma(\lambda)\le
--   c_d\bigl(\sigma^d\lambda+C(2d)^{\alpha d/2}\sigma^{-\alpha d}\bigr).
--   $$
--
--   This is the paper's approximation-error estimate for Gaussian SVMs. **Formalization Note** The dimension is positive, and $c_d$ is chosen before $\sigma$, the distribution, $\alpha$ and $C$. Distance to the empty set in $\tau_x$ is zero. The printed proof display (25) has a high-dimensional volume slip; the theorem's stated inequality is retained.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 9, Theorem 2.7 (11)

import Definitions.Def_FastRatesSVM_Rates_RKHS

namespace FastRatesSVM.Rates

/-- Theorem 2.7, arXiv:0708.1838v1, p. 9. The constant is uniform in
the kernel width, distribution, noise exponent, and noise constant. -/
theorem theorem_2_7 :
    ∀ (d : ℕ), 0 < d → ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (σ : ℝ), 0 < σ →
      ∀ (D : BinaryDistribution d) (α C : ℝ), 0 < α →
        GeometricBound D α C →
      ∀ (reg : ℝ), 0 < reg →
        approxError D σ reg ≤
          ENNReal.ofReal
            (c_d * (σ ^ d * reg + C * (2 * (d : ℝ)) ^ (α * (d : ℝ) / 2) *
              σ ^ (-(α * (d : ℝ))))) := by sorry

end FastRatesSVM.Rates
