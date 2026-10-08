-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_theorem_2_2
-- name    : ChenBullwhip.Centralized.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:37.982645+00:00
-- url     : https://prove2.me/theorems/134f2ec5-bb86-4b3f-997d-c908f6943d43
-- title:
--   Theorem 2.2 — $\mathrm{Var}(q)/\mathrm{Var}(D) \ge 1 + (2L/p + 2L^2/p^2)(1-\rho^p)$, tight when $z = 0$
-- statement:
--   **Theorem 2.2.** Let the customer demands be the steady-state AR(1) process $D_t = \mu + \rho D_{t-1} + \epsilon_t$ with $|\rho| < 1$ and errors $\epsilon_t$ i.i.d. from a symmetric distribution with mean $0$ and variance $\sigma^2 > 0$. Suppose the retailer uses a simple moving average with $p \ge 1$ demand observations and the order-up-to policy $y_t = \hat D^L_t + z\hat\sigma^L_{et}$, and orders $q_t = y_t - y_{t-1} + D_{t-1}$. Then for every period $t$, every safety factor $z$ and every constant $C_{L,\rho}$,
--
--   $$\frac{\mathrm{Var}(q_t)}{\mathrm{Var}(D_t)} \ge 1 + \left(\frac{2L}{p} + \frac{2L^2}{p^2}\right)(1-\rho^p), \tag{5}$$
--
--   and the bound is tight when $z = 0$: then the ratio equals the right-hand side.
--
--   The right-hand side exceeds $1$ whenever $L \ge 1$, so forecasting with a lead time is enough to make orders more variable than demand: this is the bullwhip effect at a single stage, quantified with an explicit constant.
--
--   **Formalization Note** "Tight when $z = 0$" is formalized as equality under $z = 0$. $\sigma > 0$ (a field of the demand structure) makes the denominator $\mathrm{Var}(D_t) = \sigma^2/(1-\rho^2)$ positive. The Gaussian special case is the published `SupplyChainTheory.bullwhip_signal_processing` (Snyder and Shen, Theorem 13.2); this statement assumes only a symmetric error law.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 438, Theorem 2.2, Eq. (5)

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem theorem_2_2 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
      ∧ (z = 0 →
          ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)) := by sorry

end ChenBullwhip.Centralized
