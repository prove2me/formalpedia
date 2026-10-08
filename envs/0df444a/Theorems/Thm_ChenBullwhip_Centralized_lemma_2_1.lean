-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_lemma_2_1
-- name    : ChenBullwhip.Centralized.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:25.231562+00:00
-- url     : https://prove2.me/theorems/b9e812a9-e2f7-4021-8c88-56729a193c19
-- title:
--   Lemma 2.1 — $\mathrm{Cov}(D_{t-i}, \hat\sigma^L_{et}) = 0$ for $i = 1, \dots, p$
-- statement:
--   **Lemma 2.1.** Let the customer demands be the steady-state AR(1) process $D_t = \mu + \rho D_{t-1} + \epsilon_t$, with errors $\epsilon_t$ i.i.d. from a symmetric distribution with mean $0$ and variance $\sigma^2$, and let $\hat\sigma^L_{et} = C_{L,\rho}\sqrt{\sum_{i=1}^p (e_{t-i})^2/p}$ be the estimate (3) of the standard deviation of the $L$-period forecast error, with window $p \ge 1$. Then for every period $t$,
--
--   $$\mathrm{Cov}(D_{t-i}, \hat\sigma^L_{et}) = 0 \qquad \text{for all } i = 1, \dots, p.$$
--
--   The paper does not prove the lemma; it refers to Ryan (1997) and Chen et al. (1998). It is what removes the cross terms between the demand part and the safety-stock part of the order in the variance computation leading to Theorem 2.2.
--
--   **Formalization Note** The constant $C_{L,\rho}$ is a free real parameter. The statement is exactly the paper's range of lags $i = 1, \dots, p$.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 438, Lemma 2.1

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem lemma_2_1 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ∀ i ∈ Finset.Icc 1 p,
      ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C p t) P = 0 := by sorry

end ChenBullwhip.Centralized
