-- Prove2me | Theorems.Thm_CalibratedCE_Generic_limitSet_subset_CESet
-- name    : CalibratedCE.Generic.limitSet_subset_CESet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:04:14.872851+00:00
-- url     : https://prove2.me/theorems/471dd3a9-66eb-4d06-9579-e574bad67e07
-- title:
--   Theorem 1 restated (p. 46) — $\lambda(G) \subseteq \pi(G)$ for every game
-- statement:
--   Let $G = (u_1,u_2)$ be any two-player game with finite strategy sets $S(1)$, $S(2)$. Let $\lambda(G)$ be the set of limit points of calibrated forecasts (the limiting joint distributions of play when each player forecasts the other with a calibrated history-dependent rule and plays a stationary deterministic best reply to the forecast), and $\pi(G)$ the set of correlated equilibria. Then
--   $$\lambda(G) \subseteq \pi(G).$$
--
--   This is the paper's Theorem 1 specialised to plays whose empirical distribution converges: "Using this notation we can restate Theorem 1 as saying that for all games $G$, $\lambda(G) \subset \pi(G)$." It gives one inclusion of Theorem 2.
--
--   **Formalization Note** The paper's $\subset$ is non-strict inclusion. The statement holds for every game, with no genericity assumption.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 46, Section 3 (Theorem 1 restated as λ(G) ⊂ π(G))

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet

namespace CalibratedCE.Generic

theorem limitSet_subset_CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) :
    LimitSet u₁ u₂ ⊆ CESet u₁ u₂ := by sorry

end CalibratedCE.Generic
