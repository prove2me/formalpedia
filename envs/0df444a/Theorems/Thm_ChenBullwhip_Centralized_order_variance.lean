-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_order_variance
-- name    : ChenBullwhip.Centralized.order_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:32.199776+00:00
-- url     : https://prove2.me/theorems/5aa514f7-a945-4c80-9f7c-155e8d1bc108
-- title:
--   Variance display after Eq. (4): $\mathrm{Var}(q_t) = [1 + (2L/p + 2L^2/p^2)(1-\rho^p)]\mathrm{Var}(D) + 2z(1+2L/p)\mathrm{Cov}(\cdot) + z^2\mathrm{Var}(\cdot)$
-- statement:
--   Under the assumptions of Lemma 2.1 (steady-state AR(1) demand with i.i.d. symmetric errors of mean $0$ and variance $\sigma^2$), for the retailer's order $q_t$ with window $p \ge 1$, lead-time parameter $L$, safety factor $z$ and constant $C_{L,\rho}$, and for every period $t$,
--
--   $$\mathrm{Var}(q_t) = \left[1 + \left(\frac{2L}{p} + \frac{2L^2}{p^2}\right)(1-\rho^p)\right]\mathrm{Var}(D) + 2z\left(1 + \frac{2L}{p}\right)\mathrm{Cov}(D_{t-1}, \hat\sigma^L_{et}) + z^2\,\mathrm{Var}(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}),$$
--
--   where $\mathrm{Var}(D) = \mathrm{Var}(D_t)$ is the common variance of the demands.
--
--   This is the final equality of the display following Eq. (4). It is true as stated, but not through the printed intermediate line: expanding $\mathrm{Var}(q_t)$ from Eq. (4) also produces the cross terms $\mathrm{Cov}(D_{t-1}, \hat\sigma^L_{e,t-1})$ and $\mathrm{Cov}(D_{t-p-1}, \hat\sigma^L_{et})$, which lie outside the lags $1, \dots, p$ of Lemma 2.1. Like every covariance between a demand and the estimate $\hat\sigma^L$, they vanish by the symmetry of the error distribution. Together with Lemma 2.1, the identity yields Theorem 2.2.
--
--   **Formalization Note** $\mathrm{Var}(D)$ is written $\mathrm{Var}(D_t)$, for the same $t$ as the order. Only the final equality of the display is formalized, because the printed first line drops cross terms.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 438, §2.2, the display following Eq. (4) (final equality)

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem order_variance {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P
      = (1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p))
            * ProbabilityTheory.variance (X.D t) P
        + 2 * z * (1 + 2 * (L : ℝ) / p)
            * ProbabilityTheory.covariance (X.D (t - 1)) (X.sigmaHat C p t) P
        + z ^ 2 * ProbabilityTheory.variance
            (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) P := by sorry

end ChenBullwhip.Centralized
