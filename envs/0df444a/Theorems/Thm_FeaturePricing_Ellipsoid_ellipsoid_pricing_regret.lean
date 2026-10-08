-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_ellipsoid_pricing_regret
-- name    : FeaturePricing.Ellipsoid.ellipsoid_pricing_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:33:14.856985+00:00
-- url     : https://prove2.me/theorems/b2bc0d2e-fbea-4a67-a20b-56d1322dd016
-- title:
--   Theorem 2, p. 11 — EllipsoidPricing with ε = Rd²/T has worst-case regret O(Rd² ln(T/d))
-- statement:
--   **Theorem 2.** The worst-case regret of the EllipsoidPricing algorithm with parameter $\epsilon=Rd^2/T$ is $O(Rd^2\ln(T/d))$.
--
--   Precisely: there is a universal constant $C>0$ such that for every dimension $d\ge2$, every $R>0$, every horizon $T\ge2d$, every parameter $\theta\in\mathbb R^d$ with $\|\theta\|\le R$, and every feature sequence $(x_t)$ with $\|x_t\|\le1$ for all $t$ (Euclidean norms), the run of EllipsoidPricing with parameter $\epsilon=Rd^2/T$ started from $E_1=B(0,R)$ satisfies
--   $$
--   \sum_{t=1}^T\big[\theta'x_t-p_t\,\mathbb I\{\theta'x_t\ge p_t\}\big]\ \le\ C\,R\,d^2\ln(T/d).
--   $$
--
--   This is the main result of the paper: a pricing policy for products described by $d$ features whose worst-case regret is polynomial (quadratic) in $d$ and logarithmic in $T$, in contrast with the exponential-in-$d$ regret of the multi-dimensional binary search (PolytopePricing, Theorem 1).
--
--   **Formalization Note** The $O(\cdot)$ is read with one constant $C$ quantified before $d,R,T,\theta$ and the features, so $C$ does not depend on the instance. The thresholds $d\ge2$ (Eq. (4) divides by $d^2-1$) and $T\ge2d$ (for $T\le d$, $\ln(T/d)\le0$ and the bound is meaningless) are added. The maximum over $\theta\in K_1$ and over nature's closed-loop strategies in Eq. (1) becomes a universal quantifier: the algorithm is deterministic, so a closed-loop nature yields a fixed feature sequence, and $K_1\subseteq\{\|\theta\|\le R\}$, so quantifying over the whole ball covers every $K_1$. The initial ellipsoid is the ball $B(0,R)$, an ellipsoid containing $K_1$ as the paper allows (p. 11). The printed proof (p. 16) bounds each exploration round's regret by $R$; that bound is not justified as printed (see the mission description), so the statement here is the $O$-claim of the theorem, not the proof's explicit inequality.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 11, Theorem 2 (regret Eq. (1), p. 8; proof pp. 15–16)

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **Theorem 2, p. 11.** The worst-case regret of EllipsoidPricing with parameter `ε = Rd²/T`,
started from `E₁ = B(0, R)`, is `O(Rd² ln(T/d))`: there is a universal constant `C > 0` such that
for every dimension `d ≥ 2`, radius `R > 0`, horizon `T ≥ 2d`, parameter `θ` with `‖θ‖ ≤ R` and
feature sequence with `‖x_t‖ ≤ 1` (Euclidean norms), the regret (1) over `T` periods is at most
`C · R · d² · ln(T/d)`. -/
theorem ellipsoid_pricing_regret :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (R : ℝ), 0 < R → ∀ (T : ℕ), 2 * d ≤ T →
      ∀ (θ : Fin d → ℝ), θ ⬝ᵥ θ ≤ R ^ 2 →
      ∀ (x : ℕ → Fin d → ℝ), (∀ t, x t ⬝ᵥ x t ≤ 1) →
        regret R (R * (d : ℝ) ^ 2 / (T : ℝ)) θ x T ≤
          C * R * (d : ℝ) ^ 2 * Real.log ((T : ℝ) / (d : ℝ)) := by sorry

end FeaturePricing.Ellipsoid
