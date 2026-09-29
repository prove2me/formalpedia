-- Prove2me | Theorems.Thm_CalibratedCE_Generic_example_limitSet_eq
-- name    : CalibratedCE.Generic.example_limitSet_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:11:50.23129+00:00
-- url     : https://prove2.me/theorems/3bd0c75f-52ef-403c-a0a8-2f7cfe4f4e02
-- title:
--   Example (p. 48) — in the $3\times3$ game, $\lambda(G)$ is the point mass on $(C,2)$
-- statement:
--   In the $3\times3$ game of p. 48 (Row's strategies $A,B,C$, Column's $1,2,3$; payoffs Row\Col: $A$: 2\2, 0\3, 0\1; $B$: 2\2, 0\1, 0\3; $C$: 2\0, 1\1, 1\0), the only limit point of calibrated forecasts is the distribution $\delta_{(C,2)}$ that puts all its weight on $(C,2)$:
--   $$\lambda(G) = \{\delta_{(C,2)}\}.$$
--
--   In the paper: "But, the only point in $\lambda(G)$ is the distribution which puts all its weight on point $(C, 2)$ which yields a payoff of $(1, 1)$." Together with the correlated equilibrium $D_0$ of payoff $(2,2)$ it shows how far $\lambda(G)$ can be from $\pi(G)$ in a non-generic game.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 48, example after the proof of Theorem 2

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet
import Definitions.Def_CalibratedCE_Generic_Example

namespace CalibratedCE.Generic

theorem example_limitSet_eq : LimitSet exU₁ exU₂ = {exDelta} := by sorry

end CalibratedCE.Generic
