-- Prove2me | Theorems.Thm_CalibratedCE_Generic_condForecast_calibrated
-- name    : CalibratedCE.Generic.condForecast_calibrated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:06:29.760751+00:00
-- url     : https://prove2.me/theorems/a5e3cea8-9aff-448a-8fce-00ab196f900d
-- title:
--   Proof of Theorem 2 (p. 47) — the conditional forecasts $p_{1,t}, p_{2,t}$ are calibrated
-- statement:
--   Let $D$ be a joint distribution over $S(1)\times S(2)$, and let $(x_t)$, $(y_t)$ be play sequences with $D(x_t,y_t) > 0$ for all $t$ whose empirical joint distribution converges to $D$: $D_t(x,y)\to D(x,y)$ for all $x,y$. Let player 1 forecast
--   $$p_{1,t}(\cdot) = \frac{D(x_t,\cdot)}{\sum_{y} D(x_t,y)}$$
--   and player 2 forecast
--   $$p_{2,t}(\cdot) = \frac{D(\cdot,y_t)}{\sum_{x} D(x,y_t)}.$$
--   Then every $p_{1,t}$ and every $p_{2,t}$ is a probability vector, the forecasts $(p_{1,t})$ are calibrated with respect to $(y_t)$, and the forecasts $(p_{2,t})$ are calibrated with respect to $(x_t)$.
--
--   In the paper: "By the assumption that the joint distribution converges to $D(x,y)$, it is clear that both of these forecasts are calibrated."
--
--   **Formalization Note** Two strategies of player 1 with the same conditional distribution produce the same forecast value; the statement covers this case (calibration is computed per forecast value, pooling those rounds). The denominator of $p_{2,t}$ is the corrected one (see the definition of the conditional forecasts).
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, proof of Theorem (Theorem 2)

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

theorem condForecast_calibrated {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (hsupp : ∀ t, 0 < D (x t) (y t))
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    (∀ t, IsDist (condForecast₁ D (x t))) ∧ (∀ t, IsDist (condForecast₂ D (y t))) ∧
      Shared.Calibrated (fun t => condForecast₁ D (x t)) y ∧
      Shared.Calibrated (fun t => condForecast₂ D (y t)) x := by sorry

end CalibratedCE.Generic
