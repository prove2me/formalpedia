-- Prove2me | Theorems.Thm_CalibratedCE_Forecast_exists_calibrated_randomized_forecast
-- name    : CalibratedCE.Forecast.exists_calibrated_randomized_forecast
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:38:46.370773+00:00
-- url     : https://prove2.me/theorems/3472903c-8fea-42dd-bdc2-cc8400ff0e91
-- title:
--   Theorem 3 — a randomized forecast calibrated against every learning rule of the opponent
-- statement:
--   Let player 2 have $n\ge 1$ pure strategies. There exists a randomized forecaster $F$ for player 1, whose forecasts are always probability vectors over player 2's strategies, such that **no matter what learning rule $A$ player 2 uses** (deterministic or randomized, depending on the whole past, but not on player 1's current forecast), player 1's calibration score
--
--   $$
--   C_t = \sum_p \sum_{j} \bigl|\rho(p,j,t) - p_j\bigr|\frac{N(p,t)}{t}
--   $$
--
--   converges to zero in probability: for every $\varepsilon>0$,
--
--   $$
--   \lim_{t\to\infty} \mathbb P_{F,A}\bigl(C_t < \varepsilon\bigr) = 1 ,
--   $$
--
--   where $\mathbb P_{F,A}$ is the law of the first $t$ rounds when forecast and play are drawn independently in each round given the past.
--
--   The forecaster is chosen first and works against every opponent; the convergence rate may depend on the opponent. By the impossibility theorem of Oakes (1985), no deterministic forecaster has this property, which is why randomization is needed.
--
--   **Formalization Note** Forecaster and opponent are maps from histories (lists of (forecast, play) pairs) to Mathlib `PMF`s; the probability of the event $\{C_t<\varepsilon\}$ is the outer measure of the history law, a value in $[0,\infty]$, and the limit is taken there. $n\ge 1$ is required: with no strategies there is no probability vector.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 49, Theorem 3 (Foster and Vohra, 1991), Eq. (1); proof in the Appendix, pp. 52–54

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH
import Definitions.Def_CalibratedCE_Forecast_HistLaw

namespace CalibratedCE.Forecast

theorem exists_calibrated_randomized_forecast (n : ℕ) (hn : 0 < n) :
    ∃ F : List ((Fin n → ℝ) × Fin n) → PMF (Fin n → ℝ),
      (∀ h, ∀ p ∈ (F h).support, IsDist p) ∧
      ∀ A : List ((Fin n → ℝ) × Fin n) → PMF (Fin n),
        ∀ ε : ℝ, 0 < ε →
          Filter.Tendsto
            (fun t : ℕ => (histLaw F A t).toOuterMeasure {h | calibScoreH h < ε})
            Filter.atTop (nhds 1) := by sorry

end CalibratedCE.Forecast
