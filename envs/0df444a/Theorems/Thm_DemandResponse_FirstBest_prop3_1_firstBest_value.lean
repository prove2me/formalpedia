-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_prop3_1_firstBest_value
-- name    : DemandResponse.FirstBest.prop3_1_firstBest_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:18:55.146261+00:00
-- url     : https://prove2.me/theorems/d013151f-8a31-47eb-8cb9-ce05b85ea54a
-- title:
--   Proposition 3.1 (i) — first-best value V^FB = U(v̄(0, X₀) − L₀) in closed form
-- statement:
--   In the electricity demand-response model of Aïd, Possamaï and Touzi, let $(f-g)(x)=\delta x$ with $\delta=\kappa-\theta$, let $V^{FB}$ be the producer's first-best value (2.6), and assume $\delta^-T\le A_{\max}$. Then
--   $$V^{FB}=U\big(\bar v(0,X_0)-L_0\big),\qquad \bar v(t,x)=\delta(T-t)x+\int_t^Tm_{FB}(s)\,ds,$$
--   where
--   $$m_{FB}(t):=\frac12\bar\mu(\delta^-)^2(T-t)^2+H_v\big(-h-\rho\delta^2(T-t)^2\big),\qquad \rho:=\frac{rp}{r+p},$$
--   $U(x)=-e^{-px}$ is the producer's utility, $L_0=-\frac1r\log(-R_0)$ is the certainty equivalent of the consumer's reservation utility, $\bar\mu=\sum_i\mu_i$, and $H_v$ is the volatility Hamiltonian (2.9).
--
--   The result gives the benchmark value of the producer when it can dictate both the payment and the consumer's effort; comparing it with the second-best value measures the cost of not observing the effort.
--
--   **Formalization Note** The hypothesis $\delta^-T\le A_{\max}$ is added. The paper's proof writes the drift part of $m_{FB}$ as $H_m(\delta(T-t))$, which equals $\frac12\bar\mu(\delta^-)^2(T-t)^2$ exactly when $\delta^-(T-t)\le A_{\max}$ and is strictly smaller otherwise, so without the hypothesis the printed formula contradicts the paper's own argument. The model's standing assumptions ($\varepsilon\le1$, $R_0<0$ included) are the fields of `Params`.
-- source:
--   arXiv:1810.09063v3, Proposition 3.1 (i) (p. 10)

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model
import Definitions.Def_DemandResponse_FirstBest_ClosedForm

namespace DemandResponse.FirstBest

/-- Proposition 3.1 (i) (first-best value): for `(f - g)(x) = δ x` and `δ⁻ T ≤ Amax`,
`V^FB = U(v̄(0, X₀) - L₀)` with `v̄(t, x) = δ(T - t)x + ∫ₜᵀ m_FB(s) ds`. -/
theorem prop3_1_firstBest_value {N d : ℕ} (P : Params N d)
    (hA : xneg (delta P) * P.T ≤ P.Amax) :
    VFB P = ((U P (vbarFB P 0 P.X₀ - L0 P) : ℝ) : EReal) := by sorry

end DemandResponse.FirstBest
