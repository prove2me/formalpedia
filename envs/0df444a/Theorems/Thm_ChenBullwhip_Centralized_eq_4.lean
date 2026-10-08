-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_eq_4
-- name    : ChenBullwhip.Centralized.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:21.1386+00:00
-- url     : https://prove2.me/theorems/0d21cb2d-792a-4945-afc2-590cece1a98a
-- title:
--   Eq. (4): $q_t = (1 + L/p)D_{t-1} - (L/p)D_{t-p-1} + z(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1})$
-- statement:
--   For the retailer's moving-average order-up-to policy with window $p \ge 1$, lead-time parameter $L$, safety factor $z$ and constant $C_{L,\rho}$, the order $q_t = y_t - y_{t-1} + D_{t-1}$ satisfies, for every period $t$ and every outcome,
--
--   $$q_t = L\left(\frac{D_{t-1} - D_{t-p-1}}{p}\right) + D_{t-1} + z(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}) = \left(1 + \frac{L}{p}\right)D_{t-1} - \frac{L}{p}\,D_{t-p-1} + z(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}). \tag{4}$$
--
--   The two moving averages $\hat D^L_t$ and $\hat D^L_{t-1}$ share all but their first and last terms. The identity reduces the order to two demands $p$ periods apart plus a safety-stock correction, and it is the starting point of the variance computation behind Theorem 2.2.
--
--   **Formalization Note** This is a pathwise identity: it holds for every outcome $\omega$ and its proof uses no distributional fact. The demand model is on a probability space. $L/p$ is real division and $p \ge 1$ is assumed.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 438, Eq. (4)

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem eq_4 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p) (t : ℤ) (ω : Ω) :
    X.order C z L p t ω
        = (L : ℝ) * ((X.D (t - 1) ω - X.D (t - p - 1) ω) / p) + X.D (t - 1) ω
          + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω)
      ∧ X.order C z L p t ω
        = (1 + (L : ℝ) / p) * X.D (t - 1) ω - ((L : ℝ) / p) * X.D (t - p - 1) ω
          + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) := by sorry

end ChenBullwhip.Centralized
