-- Prove2me | Theorems.Thm_FDivToolkit_lemma_3
-- name    : FDivToolkit.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:04.459878+00:00
-- url     : https://prove2.me/theorems/3ce5e86f-e5f4-4aaf-be0b-5946c7154e61
-- title:
--   Lemma 3 — properties of the Weibull $H$
-- statement:
--   Let $k>0$, $\theta>\max\{k,1\}$, and let $H$ be the function of (10). Then:
--
--   1. $H$ is continuous and strictly increasing, with $\lim_{y\to\infty}H(y)=\infty$ and $H(0)=0$, so it is a generating function;
--   2. $L=\lim_{y\to-\infty}H(y)=-\infty$;
--   3. $H$ is convex;
--   4. $H$ is continuously differentiable with $H'(0)=1$;
--   5. $H$ is increasing in $\theta$: for $\theta\le\theta'$, $H_\theta(y)\le H_{\theta'}(y)$ for all $y\in\mathbb R$.
--
--   This makes the general results of §2 applicable to $H$. Monotonicity in $\theta$ shows that the divergence grows with $\theta$, so a ball of fixed radius shrinks as more moments are imposed.
--
--   Differences from the source:
--   - reading: H is increasing in θ → for θ ≤ θ′, H_θ(y) ≤ H_θ′(y) for all y (weak, pointwise); reason: the strict reading is false: H_θ(y) = y = H_θ′(y) for y < 0
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Lemma 3, p.13

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_weibullH

open Filter

namespace FDivToolkit

/-- Lemma 3, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.13: the Weibull `H` of (10)
is strictly increasing with `lim_{y→∞} H(y) = ∞`, `H(0) = 0` and `L = lim_{y→−∞} H(y) = −∞`; it is
convex and continuously differentiable with `H′(0) = 1`; and it is increasing in `θ`.

**Formalization Note.** `IsAdmissibleH` carries monotonicity, the limit at `+∞`, `H(0) = 0` and
continuity. "Increasing in `θ`" is pointwise and weak, as `H` does not depend on `θ` on `y < 0`. -/
theorem lemma_3 {k θ : ℝ} (hk : 0 < k) (hθ : max k 1 < θ) :
    IsAdmissibleH (weibullH k θ) ∧
    Tendsto (weibullH k θ) atBot atBot ∧
    ConvexOn ℝ Set.univ (weibullH k θ) ∧
    ContDiff ℝ 1 (weibullH k θ) ∧
    deriv (weibullH k θ) 0 = 1 ∧
    ∀ θ' : ℝ, θ ≤ θ' → ∀ y : ℝ, weibullH k θ y ≤ weibullH k θ' y := by sorry

end FDivToolkit
