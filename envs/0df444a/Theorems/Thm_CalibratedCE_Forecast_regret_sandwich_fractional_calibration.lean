-- Prove2me | Theorems.Thm_CalibratedCE_Forecast_regret_sandwich_fractional_calibration
-- name    : CalibratedCE.Forecast.regret_sandwich_fractional_calibration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:37:46.785266+00:00
-- url     : https://prove2.me/theorems/433c55ec-e349-4094-b433-c351ab0313b4
-- title:
--   Appendix (p. 54) — the regrets sandwich the fractional L-2 calibration score
-- statement:
--   Let $k\ge 1$, let $p^1,\dots,p^k$ be probability vectors over player 2's $n$ strategies, and let $\varepsilon\in\mathbb R$ be such that every probability vector $q$ over the $n$ strategies is within squared distance $\varepsilon$ of the grid: $\min_i \sum_j (q_j - p^i_j)^2 \le \varepsilon$. Let $X_t$ be player 2's plays (as 0–1 vectors), let $w_t$ be any probability vectors on $\{1,\dots,k\}$, and use the losses $L_t^i = |X_t - p^i|^2$ in the regrets $R_T^{i\to j}$. Then for every $T$,
--
--   $$
--   \sum_{i=1}^{k} \max_{j} \frac{R_T^{i\to j}}{T} \;\le\; C_{2,w}(T) \;\le\; \varepsilon + \sum_{i=1}^{k}\max_{j} \frac{R_T^{i\to j}}{T},
--   $$
--
--   where $C_{2,w}(T) = \sum_i\sum_j (\rho_w(i,j,T) - p^i_j)^2 N_w(i,T)/T$ is the fractional L-2 calibration score (the calibration score with the event "forecast $p^i$ in round $t$" replaced by its probability $w_t^i$).
--
--   Combined with Lemma 1, it converts the no-regret property of the forecaster into calibration.
--
--   **Formalization Note** The page writes the middle term as $E(C_2(t))$ with a typographically garbled formula; the statement pins the quantity for which the displayed inequalities hold, the fractional score $C_{2,w}$. "Within $\varepsilon$" is read in squared Euclidean distance, the reading under which the right-hand inequality holds with $\varepsilon$ (not $\varepsilon^2$). The grid is indexed $1,\dots,k$, as in Lemma 1. Rounds are $0,\dots,T-1$; the maximum over $j$ is a finite maximum (`Finset.sup'`).
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), pp. 53–54, Appendix ("Simple algebra yields"), pinned reading

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_Regret
import Definitions.Def_CalibratedCE_Forecast_FracCalib

namespace CalibratedCE.Forecast

theorem regret_sandwich_fractional_calibration {k n : ℕ} (hk : 0 < k) (ε : ℝ)
    (p : Fin k → Fin n → ℝ) (hp : ∀ i, IsDist (p i))
    (hgrid : ∀ q : Fin n → ℝ, IsDist q → ∃ i, ∑ j, (q j - p i j) ^ 2 ≤ ε)
    (X : ℕ → Fin n) (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (T : ℕ) :
    ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) ≤ C2w p w X T ∧
    C2w p w X T ≤ ε + ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) := by sorry

end CalibratedCE.Forecast
