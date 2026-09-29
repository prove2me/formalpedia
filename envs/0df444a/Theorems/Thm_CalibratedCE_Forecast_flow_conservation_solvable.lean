-- Prove2me | Theorems.Thm_CalibratedCE_Forecast_flow_conservation_solvable
-- name    : CalibratedCE.Forecast.flow_conservation_solvable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:36:44.19364+00:00
-- url     : https://prove2.me/theorems/aa4de036-23ef-4b79-925a-a65f1639e6e9
-- title:
--   Appendix (p. 52) — flow conservation equations have a probability-vector solution
-- statement:
--   Let $k\ge 1$ and let $R = (R^{i\to j})_{i,j=1}^k$ be any matrix of nonnegative reals. Then there is a probability vector $w = (w^1,\dots,w^k)$ ($w^i\ge 0$, $\sum_i w^i = 1$) satisfying the **flow conservation equations**
--
--   $$
--   w^i \sum_{j=1}^{k} R^{i\to j} \;=\; \sum_{j=1}^{k} w^j R^{j\to i} \qquad (i = 1,\dots,k).
--   $$
--
--   In the Appendix the matrix is that of the regrets $R_{t-1}^{i\to j}$ after $t-1$ rounds, and a solution $w_t$ is the forecaster's mixture in round $t$; the paper invokes linear programming duality for its existence. Equivalently, $w$ is a stationary distribution of the finite Markov chain that moves from $i$ to $j$ at a rate proportional to $R^{i\to j}$.
--
--   **Formalization Note** The statement is made for an arbitrary nonnegative matrix, not only for regret matrices; this is the form the paper's existence claim takes. $k\ge 1$ is needed: there is no probability vector on an empty index set.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 52, Appendix (flow conservation equations and their solvability)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace CalibratedCE.Forecast

theorem flow_conservation_solvable (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ)
    (hR : ∀ i j, 0 ≤ R i j) :
    ∃ w : Fin k → ℝ, IsDist w ∧ ∀ i, w i * ∑ j, R i j = ∑ j, w j * R j i := by sorry

end CalibratedCE.Forecast
