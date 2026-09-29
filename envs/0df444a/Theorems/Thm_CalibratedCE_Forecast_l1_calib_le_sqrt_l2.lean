-- Prove2me | Theorems.Thm_CalibratedCE_Forecast_l1_calib_le_sqrt_l2
-- name    : CalibratedCE.Forecast.l1_calib_le_sqrt_l2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:38:17.081419+00:00
-- url     : https://prove2.me/theorems/13d66600-77d7-4614-8484-5a384f8493f9
-- title:
--   Appendix (p. 54) — L-1 calibration is at most the square root of L-2 calibration
-- statement:
--   For every finite history of forecasts and plays of length $t$ and every strategy $j$ of player 2,
--
--   $$
--   \sum_p \bigl|\rho(p,j,t) - p_j\bigr|\frac{N(p,t)}{t} \;\le\; \sqrt{\sum_p \bigl(\rho(p,j,t) - p_j\bigr)^2 \frac{N(p,t)}{t}} ,
--   $$
--
--   that is, the L-1 calibration score for $j$ is at most the square root of the L-2 calibration score $C_2(t)$ for $j$. Summing over $j$ bounds the calibration score $C_t$ of Eq. (1) by $\sum_j \sqrt{C_2^{(j)}(t)}$, which is how the Appendix passes from L-2 calibration to the L-1 calibration of Theorem 3.
--
--   **Formalization Note** "Smaller" is read as $\le$ (equality is possible). The sums run over the forecasts occurring in the history; for the empty history both sides are $0$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 54, Appendix (L-1 calibration versus the square root of L-2 calibration)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH

namespace CalibratedCE.Forecast

theorem l1_calib_le_sqrt_l2 {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by sorry

end CalibratedCE.Forecast
