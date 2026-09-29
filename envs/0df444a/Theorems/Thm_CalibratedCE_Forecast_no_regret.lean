-- Prove2me | Theorems.Thm_CalibratedCE_Forecast_no_regret
-- name    : CalibratedCE.Forecast.no_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:37:11.240505+00:00
-- url     : https://prove2.me/theorems/95a230f9-0faf-46a8-b7a9-059c25ea232b
-- title:
--   Lemma 1 (No-Regret) — pairwise regret at most $\sqrt{2kT}$
-- statement:
--   Consider $k$ forecasts with losses $0\le L_t^i\le 1$, and a combined forecast that uses forecast $i$ in round $t$ with probability $w_t^i$, where each $w_t$ is a probability vector satisfying the flow conservation equations for the regrets of the previous rounds:
--
--   $$
--   w_t^i \sum_{j=1}^k R_{t-1}^{i\to j} = \sum_{j=1}^k w_t^j R_{t-1}^{j\to i} \qquad\text{for every } i .
--   $$
--
--   Here $R_T^{i\to j} = \max\{0,\sum_{t=1}^T w_t^i(L_t^i - L_t^j)\}$ is the regret of changing all $i$ forecasts to $j$ forecasts. Then for all $i^*, j^*$ and every $T$,
--
--   $$
--   R_T^{i^*\to j^*} \;\le\; \sqrt{2kT}.
--   $$
--
--   This is the "no-regret" property on which the Appendix builds the calibrated forecast of Theorem 3.
--
--   **Formalization Note** Rounds are indexed from $0$; the hypothesis at $0$-based round $t$ uses the regrets over rounds $0,\dots,t-1$ (the paper's $R_{t-1}$). At round $0$ every regret is $0$, so the condition holds for every $w_0$, as on the page. The weights $w_t$ may depend on anything, including $L_t$; the inequality is deterministic. The losses and weights are real sequences; nothing is assumed about how they were generated.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 52, Lemma 1 (No-Regret)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_Regret

namespace CalibratedCE.Forecast

theorem no_regret (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) (i j : Fin k) :
    Rg L w T i j ≤ Real.sqrt (2 * k * T) := by sorry

end CalibratedCE.Forecast
