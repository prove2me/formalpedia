-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_ar1_moments
-- name    : ChenBullwhip.Centralized.ar1_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:13.127596+00:00
-- url     : https://prove2.me/theorems/d8755c03-aa31-45a8-b736-0491d00f1c90
-- title:
--   AR(1) moments: $\mathrm{Var}(D_t) = \sigma^2/(1-\rho^2)$ and $\mathrm{Cov}(D_{t-1}, D_{t-p-1}) = \rho^p\sigma^2/(1-\rho^2)$
-- statement:
--   Let $(D_t)_{t \in \mathbb Z}$ be the steady-state AR(1) demand $D_t = \mu + \rho D_{t-1} + \epsilon_t$ with $|\rho| < 1$ and errors i.i.d. from a symmetric distribution with mean $0$ and variance $\sigma^2$. Then for every period $t$ and every forecast window $p \ge 1$,
--
--   $$\mathrm{Cov}(D_{t-1}, D_{t-p-1}) = \frac{\rho^p}{1-\rho^2}\,\sigma^2 \qquad\text{and}\qquad \mathrm{Var}(D_t) = \frac{\sigma^2}{1-\rho^2}.$$
--
--   These are the two facts the paper invokes to pass from the first to the second line of the variance computation after Eq. (4): the two demands entering the order, $D_{t-1}$ and $D_{t-p-1}$, are $p$ periods apart, which is where the factor $1-\rho^p$ of the bullwhip bound comes from.
--
--   **Formalization Note** The variance formula is the one asserted on p. 437 after Eq. (1); $p$ is the positive forecast window used in the covariance formula on p. 438.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 438, §2.2, the sentence after the display following Eq. (4) (Var(D_t) also asserted on p. 437)

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem ar1_moments {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    ProbabilityTheory.covariance (X.D (t - 1)) (X.D (t - p - 1)) P
        = X.rho ^ p / (1 - X.rho ^ 2) * X.sigma ^ 2
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by sorry

end ChenBullwhip.Centralized
