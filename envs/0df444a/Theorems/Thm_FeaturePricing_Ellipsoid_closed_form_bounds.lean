-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_closed_form_bounds
-- name    : FeaturePricing.Ellipsoid.closed_form_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:32:03.777643+00:00
-- url     : https://prove2.me/theorems/2b70ab71-0769-4a63-b4ff-5e0bc3da0c2f
-- title:
--   §5.2, p. 15 — min/max of x′θ over E(A, a) are x′a ∓ √(x′Ax)
-- statement:
--   Let $A$ be a positive definite $d\times d$ matrix, $a\in\mathbb R^d$, and $E(A,a)=\{\theta:(\theta-a)'A^{-1}(\theta-a)\le1\}$. For every $x\in\mathbb R^d$,
--   $$
--   \min_{\theta\in E(A,a)}x'\theta = x'a-\sqrt{x'Ax},\qquad \max_{\theta\in E(A,a)}x'\theta = x'a+\sqrt{x'Ax},
--   $$
--   and both extrema are attained.
--
--   These closed forms turn the two optimization problems (3) of EllipsoidPricing into a matrix–vector product; they are the formulas the algorithm's definition uses for $\underline b_t$ and $\bar b_t$, and in particular they give the gap $\bar b_t-\underline b_t=2\sqrt{x_t'A_tx_t}$.
--
--   **Formalization Note** Stated as `IsLeast` and `IsGreatest` of the image of $E(A,a)$ under $\theta\mapsto x'\theta$. The paper states it for $x\ne0$ (with minimizer $a-Ax/\sqrt{x'Ax}$); for $x=0$ both sides equal $0$, so no hypothesis $x\ne0$ is needed.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 15, §5.2 (closed form of Eq. (3)); also p. 14, §5.1

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **§5.2, p. 15.** For a positive definite `A`, the minimum and maximum of `θ ↦ x′θ` over the
ellipsoid `E(A, a)` are `x′a − √(x′Ax)` and `x′a + √(x′Ax)` (the closed forms of Eq. (3)). -/
theorem closed_form_bounds {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x : Fin d → ℝ) :
    IsLeast ((fun θ => x ⬝ᵥ θ) '' ellipsoid a A) (x ⬝ᵥ a - Real.sqrt (x ⬝ᵥ A *ᵥ x)) ∧
    IsGreatest ((fun θ => x ⬝ᵥ θ) '' ellipsoid a A) (x ⬝ᵥ a + Real.sqrt (x ⬝ᵥ A *ᵥ x)) := by sorry

end FeaturePricing.Ellipsoid
