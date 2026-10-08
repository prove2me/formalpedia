-- Prove2me | Theorems.Thm_AsympCalib_Main_variance_bounds
-- name    : AsympCalib.Main.variance_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:44.605956+00:00
-- url     : https://prove2.me/theorems/f40ebf86-62a6-4f95-a532-301da853ecfb
-- title:
--   §6, p. 386 — second-moment bounds for the two counting errors
-- statement:
--   Fix $k\ge1$, any history-dependent randomized grid forecaster $\sigma$, any adaptive randomized Nature $A$, a grid point $i/k$, and $t\ge1$. Let $n_t(i/k)$ count the realized forecasts of $i/k$, let $\widetilde n_t(i/k)$ sum their conditional forecast probabilities, and let $\rho_t n_t$ and $\widetilde\rho_t\widetilde n_t$ be the corresponding realized and weighted numbers of wet outcomes. Under the law of the first $t$ rounds,
--
--   $$
--   \mathbb E\!\left[\left(\frac{n_t(i/k)-\widetilde n_t(i/k)}t\right)^2\right]\le\frac1t,
--   \qquad
--   \mathbb E\!\left[\left(\frac{\rho_t n_t-\widetilde\rho_t\widetilde n_t}{t}\right)^2\right]\le\frac1t.
--   $$
--
--   These bounds control the random difference between observed and conditional forecast counts in Theorem 2.
--
--   **Formalization Note** The paper says “variance”; each error is a mean-zero martingale, so its variance equals its second moment. The expectation is a sum of probability weights over finite histories. Round $s$ uses the distribution from the prefix before $s$. The condition $k>0$ identifies distinct grid probabilities, and $t>0$ makes the displayed normalization nondegenerate.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 386, §6, proof of Theorem 2, final variance displays; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem variance_bounds (k : ℕ) (hk : 0 < k)
    (σ : History → PMF (Fin (k + 1)))
    (A : History → PMF (Fin 2))
    (t : ℕ) (ht : 0 < t) (i : Fin (k + 1)) :
    (∑' h : History,
      ((CalibratedCE.Forecast.histLaw (forecaster k σ) A t) h).toReal *
        (((CalibratedCE.Forecast.NH h (gridVec k i) : ℝ) -
          nTilde k (muH σ h) t i) / (t : ℝ)) ^ 2) ≤ 1 / (t : ℝ) ∧
    (∑' h : History,
      ((CalibratedCE.Forecast.histLaw (forecaster k σ) A t) h).toReal *
        ((CalibratedCE.Forecast.rhoH h (gridVec k i) 1 *
            (CalibratedCE.Forecast.NH h (gridVec k i) : ℝ) -
          ∑ s ∈ Finset.range t, muH σ h s i * outcomeR h s) / (t : ℝ)) ^ 2) ≤
      1 / (t : ℝ) := by sorry

end AsympCalib.Main
