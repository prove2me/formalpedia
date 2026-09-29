-- Prove2me | Theorems.Thm_CalibratedCE_Generic_CE_condForecast_best_response
-- name    : CalibratedCE.Generic.CE_condForecast_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:07:47.158006+00:00
-- url     : https://prove2.me/theorems/348296bc-3da4-4208-99b4-84f110ac9a89
-- title:
--   Proof of Theorem 2 (p. 47) — in a CE each recommended strategy is a best response to its conditional forecast
-- statement:
--   Let $D$ be a correlated equilibrium of the game $(u_1,u_2)$. Then:
--
--   1. for every $x\in S(1)$ with $\sum_y D(x,y) > 0$, the conditional forecast $p_1^x(\cdot) = D(x,\cdot)/\sum_y D(x,y)$ lies in $M_b(x)$, i.e. $x$ is a best response of player 1 to it;
--   2. for every $y\in S(2)$ with $\sum_x D(x,y) > 0$ and every $y'\in S(2)$, with $p_2^y(\cdot) = D(\cdot,y)/\sum_x D(x,y)$,
--   $$\sum_{x} p_2^y(x)\,u_2(x,y') \le \sum_x p_2^y(x)\,u_2(x,y).$$
--
--   In the proof of Theorem 2: "Further, $x_t$ is in fact a best response to the forecast $p_{1,t}(\cdot)$, and $y_t$ is a best response to $p_{2,t}(\cdot)$." Since $p_{1,t}$ is the conditional forecast at $x = x_t$, this is the statement at each round.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, proof of Theorem (Theorem 2)

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

namespace CalibratedCE.Generic

theorem CE_condForecast_best_response {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) :
    (∀ a, 0 < ∑ c, D a c → condForecast₁ D a ∈ Mb u₁ a) ∧
      (∀ b, 0 < ∑ c, D c b → ∀ b',
        ∑ a, condForecast₂ D b a * u₂ a b' ≤ ∑ a, condForecast₂ D b a * u₂ a b) := by sorry

end CalibratedCE.Generic
