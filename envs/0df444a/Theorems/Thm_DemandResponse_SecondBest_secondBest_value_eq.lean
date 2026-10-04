-- Prove2me | Theorems.Thm_DemandResponse_SecondBest_secondBest_value_eq
-- name    : DemandResponse.SecondBest.secondBest_value_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:05:37.035763+00:00
-- url     : https://prove2.me/theorems/7fc5757f-36a1-4806-bb66-9ce0aa352790
-- title:
--   Proposition 3.2 (i) — the producer's second-best value is $V^{SB}=U(v(0,X_0)-L_0)$
-- statement:
--   Consider the demand-response contracting problem of Sections 2.1-2.2: a consumer with CARA risk aversion $r>0$ controls the drift (effort $\alpha\in A$) and the volatility (effort $\beta\in[\varepsilon,1]^d$) of his consumption $X$, at cost $c_1(\alpha)+\frac12c_2(\beta)$ per unit time; a producer with CARA risk aversion $p>0$, who observes only $X$, offers an $\mathcal F_T$-measurable payment $\xi$ in the contract class $\mathcal C$; the consumer responds optimally, and the producer maximises $\mathbb E[U(-\xi-\int_0^T\theta X_sds-\frac h2\langle X\rangle_T)]$ subject to the participation constraint $V_A(\xi)\ge R_0$. Let $V^{SB}$ be the producer's second-best value (2.7).
--
--   Assume $(f-g)(x)=\delta x$ with $\delta=\kappa-\theta$ and $\delta^-T\le A_{\max}$. Then
--   $$V^{SB}=U\big(v(0,X_0)-L_0\big)=-\exp\Big(-p\big(v(0,X_0)-L_0\big)\Big),$$
--   where $L_0=-\frac1r\log(-R_0)$ and
--   $$v(0,X_0)=\delta TX_0+\int_0^Tm_{SB}(s)\,ds,\qquad m_{SB}(t)=\frac12\bar\mu\,\delta^2(T-t)^2-\frac12\inf_{z\in\mathbb R}\Big\{\bar\mu\big(z^-+\delta(T-t)\big)^2-2H_v\big(-q_t(z)\big)\Big\},$$
--   with $q_t(z)=h+rz^2+p(z-\delta(T-t))^2$.
--
--   The second-best value is thus explicit up to a scalar minimisation over the payment rate $z$ at each time; it is the benchmark against which the paper measures the cost of moral hazard and the value of responsiveness incentives.
--
--   **Formalization Note.** The value is an extended real, computed from the model definitions (`DemandResponse.SecondBest.Model`), and the right-hand side is a real number. Three departures from the page, all disclosed: (1) the page prints $-2H_m(-q(z))$ in $m_{SB}$, a misprint for $-2H_v(-q(z))$ (with $H_m$ the infimum is $-\infty$; the proof uses $F_0(q)=-2H_v(-q)$); (2) the hypothesis $\delta^-T\le A_{\max}$ is added: the paper's closed form is derived with the effort cap dropped ("$\eta_A\to0$ as $A\nearrow\infty$", p. 30), while the model caps the effort at $\mu_iA_{\max}$, and the two agree exactly when $\delta^-T\le A_{\max}$; (3) the model is a weak formulation by a martingale problem, with $\langle X\rangle_T$ read as $\int_0^T|\sigma(\beta_s)|^2ds$ (see the Model definition). $R_0<0$ and $\varepsilon\le1$ are fields of `Params`.
-- source:
--   arXiv:1810.09063v3, Proposition 3.2 (i) (p. 11); model Sections 2.1-2.2 (pp. 7-9); proof Appendix A.3 (pp. 28-31)

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_ClosedForm
import Definitions.Def_DemandResponse_SecondBest_Model

namespace DemandResponse.SecondBest

/-- Proposition 3.2 (i) (arXiv:1810.09063v3, p. 11): with `(f - g)(x) = δ x`, the producer's second-best
value is `V^SB = U(v(0, X₀) - L₀)`, where `v(0, X₀) = δ T X₀ + ∫₀ᵀ m_SB(s) ds` (printed `H_m` corrected to
`H_v` in `m_SB`), under the added hypothesis `δ⁻ T ≤ A_max`. -/
theorem secondBest_value_eq {N d : ℕ} (P : Params N d) (hcap : negp (delta P) * P.T ≤ P.Amax) :
    VSB P = ((Uprod P (v0 P - L0 P) : ℝ) : EReal) := by sorry

end DemandResponse.SecondBest
